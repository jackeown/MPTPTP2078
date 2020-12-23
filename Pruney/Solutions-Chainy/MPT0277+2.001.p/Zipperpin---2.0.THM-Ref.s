%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c2sk5cyQBu

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:40 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :  221 (2282 expanded)
%              Number of leaves         :   26 ( 738 expanded)
%              Depth                    :   32
%              Number of atoms          : 1941 (20160 expanded)
%              Number of equality atoms :  274 (2872 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t75_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) )
        = k1_xboole_0 )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) )
          = k1_xboole_0 )
      <=> ~ ( ( A != k1_xboole_0 )
            & ( A
             != ( k1_tarski @ B ) )
            & ( A
             != ( k1_tarski @ C ) )
            & ( A
             != ( k2_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_zfmisc_1])).

thf('0',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
     != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 )
    | ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    sk_A
 != ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['7','17'])).

thf('19',plain,(
    sk_A
 != ( k2_tarski @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['6','18'])).

thf('20',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','19'])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('22',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

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

thf('24',plain,(
    ! [X48: $i,X50: $i,X51: $i] :
      ( ( r1_tarski @ X50 @ ( k2_tarski @ X48 @ X51 ) )
      | ( X50
       != ( k1_tarski @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('25',plain,(
    ! [X48: $i,X51: $i] :
      ( r1_tarski @ ( k1_tarski @ X51 ) @ ( k2_tarski @ X48 @ X51 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('36',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('38',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','43'])).

thf('45',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ X0 @ sk_C ) )
          = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ( sk_A
          = ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','46'])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('49',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X48: $i,X50: $i,X51: $i] :
      ( ( r1_tarski @ X50 @ ( k2_tarski @ X48 @ X51 ) )
      | ( X50
       != ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('52',plain,(
    ! [X48: $i,X51: $i] :
      ( r1_tarski @ ( k1_tarski @ X48 ) @ ( k2_tarski @ X48 @ X51 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ X0 ) )
          = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','58'])).

thf('60',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('61',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('64',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('66',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('69',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['68','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['63','74'])).

thf('76',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('78',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X19 @ X18 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('79',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('84',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('85',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('88',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['82','89'])).

thf('91',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('92',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['82','89'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['82','89'])).

thf('97',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['94','95','96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['82','89'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','100'])).

thf('102',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','62','101'])).

thf('103',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['103'])).

thf('105',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','104'])).

thf('106',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('108',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('109',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['68','72','73'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['107','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['106','113'])).

thf('115',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['105','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('117',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['107','112'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['107','112'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['63','74'])).

thf('128',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['115','126','127'])).

thf('129',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k5_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ) ) ) ),
    inference('sup+',[status(thm)],['128','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('138',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['107','112'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['106','113'])).

thf('145',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['136','143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('147',plain,
    ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_A ) @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['63','74'])).

thf('150',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('152',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('153',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['151','154'])).

thf('156',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['150','161'])).

thf('163',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['107','112'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('173',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['162','171','172'])).

thf('174',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('175',plain,(
    r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X50
        = ( k2_tarski @ X48 @ X49 ) )
      | ( X50
        = ( k1_tarski @ X49 ) )
      | ( X50
        = ( k1_tarski @ X48 ) )
      | ( X50 = k1_xboole_0 )
      | ~ ( r1_tarski @ X50 @ ( k2_tarski @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('177',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    sk_A
 != ( k2_tarski @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['6','18'])).

thf('179',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
   <= ( sk_A
     != ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['179'])).

thf('181',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['179'])).

thf('182',plain,(
    sk_A
 != ( k1_tarski @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['103','181'])).

thf('183',plain,(
    sk_A
 != ( k1_tarski @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['180','182'])).

thf('184',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['184'])).

thf('186',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['184'])).

thf('187',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['103','186'])).

thf('188',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['185','187'])).

thf('189',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('190',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('191',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['103','190'])).

thf('192',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['189','191'])).

thf('193',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['177','178','183','188','192'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c2sk5cyQBu
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.21/1.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.21/1.45  % Solved by: fo/fo7.sh
% 1.21/1.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.21/1.45  % done 2530 iterations in 0.969s
% 1.21/1.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.21/1.45  % SZS output start Refutation
% 1.21/1.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.21/1.45  thf(sk_A_type, type, sk_A: $i).
% 1.21/1.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.21/1.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.21/1.45  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.21/1.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.21/1.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.21/1.45  thf(sk_C_type, type, sk_C: $i).
% 1.21/1.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.21/1.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.21/1.45  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.21/1.45  thf(sk_B_type, type, sk_B: $i).
% 1.21/1.45  thf(t75_zfmisc_1, conjecture,
% 1.21/1.45    (![A:$i,B:$i,C:$i]:
% 1.21/1.45     ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 1.21/1.45       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 1.21/1.45            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 1.21/1.45  thf(zf_stmt_0, negated_conjecture,
% 1.21/1.45    (~( ![A:$i,B:$i,C:$i]:
% 1.21/1.45        ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 1.21/1.45          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 1.21/1.45               ( ( A ) != ( k1_tarski @ C ) ) & 
% 1.21/1.45               ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ) )),
% 1.21/1.45    inference('cnf.neg', [status(esa)], [t75_zfmisc_1])).
% 1.21/1.45  thf('0', plain,
% 1.21/1.45      ((((sk_A) = (k2_tarski @ sk_B @ sk_C))
% 1.21/1.45        | ((sk_A) = (k1_tarski @ sk_C))
% 1.21/1.45        | ((sk_A) = (k1_tarski @ sk_B))
% 1.21/1.45        | ((sk_A) = (k1_xboole_0))
% 1.21/1.45        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 1.21/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.45  thf('1', plain,
% 1.21/1.45      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))
% 1.21/1.45         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 1.21/1.45      inference('split', [status(esa)], ['0'])).
% 1.21/1.45  thf('2', plain,
% 1.21/1.45      ((((sk_A) != (k1_xboole_0))
% 1.21/1.45        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 1.21/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.45  thf('3', plain,
% 1.21/1.45      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 1.21/1.45         <= (~
% 1.21/1.45             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 1.21/1.45      inference('split', [status(esa)], ['2'])).
% 1.21/1.45  thf('4', plain,
% 1.21/1.45      ((((sk_A) = (k2_tarski @ sk_B @ sk_C))
% 1.21/1.45        | ((sk_A) = (k1_tarski @ sk_C))
% 1.21/1.45        | ((sk_A) = (k1_tarski @ sk_B))
% 1.21/1.45        | ((sk_A) = (k1_xboole_0))
% 1.21/1.45        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 1.21/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.45  thf('5', plain,
% 1.21/1.45      ((((sk_A) != (k2_tarski @ sk_B @ sk_C))
% 1.21/1.45        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 1.21/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.45  thf('6', plain,
% 1.21/1.45      ((((sk_A) != (k2_tarski @ sk_B @ sk_C)))
% 1.21/1.45         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 1.21/1.45      inference('split', [status(esa)], ['5'])).
% 1.21/1.45  thf('7', plain,
% 1.21/1.45      (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) | 
% 1.21/1.45       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 1.21/1.45      inference('split', [status(esa)], ['5'])).
% 1.21/1.45  thf(t92_xboole_1, axiom,
% 1.21/1.45    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.21/1.45  thf('8', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 1.21/1.45      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.21/1.45  thf(idempotence_k3_xboole_0, axiom,
% 1.21/1.45    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.21/1.45  thf('9', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.21/1.45      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.21/1.45  thf(t100_xboole_1, axiom,
% 1.21/1.45    (![A:$i,B:$i]:
% 1.21/1.45     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.21/1.45  thf('10', plain,
% 1.21/1.45      (![X4 : $i, X5 : $i]:
% 1.21/1.45         ((k4_xboole_0 @ X4 @ X5)
% 1.21/1.45           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.21/1.45  thf('11', plain,
% 1.21/1.45      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['9', '10'])).
% 1.21/1.45  thf('12', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 1.21/1.45      inference('demod', [status(thm)], ['8', '11'])).
% 1.21/1.45  thf('13', plain,
% 1.21/1.45      ((((sk_A) = (k2_tarski @ sk_B @ sk_C)))
% 1.21/1.45         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 1.21/1.45      inference('split', [status(esa)], ['0'])).
% 1.21/1.45  thf('14', plain,
% 1.21/1.45      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 1.21/1.45         <= (~
% 1.21/1.45             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 1.21/1.45      inference('split', [status(esa)], ['2'])).
% 1.21/1.45  thf('15', plain,
% 1.21/1.45      ((((k4_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0)))
% 1.21/1.45         <= (~
% 1.21/1.45             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 1.21/1.45             (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 1.21/1.45      inference('sup-', [status(thm)], ['13', '14'])).
% 1.21/1.45  thf('16', plain,
% 1.21/1.45      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.21/1.45         <= (~
% 1.21/1.45             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 1.21/1.45             (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 1.21/1.45      inference('sup-', [status(thm)], ['12', '15'])).
% 1.21/1.45  thf('17', plain,
% 1.21/1.45      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 1.21/1.45       ~ (((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 1.21/1.45      inference('simplify', [status(thm)], ['16'])).
% 1.21/1.45  thf('18', plain, (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 1.21/1.45      inference('sat_resolution*', [status(thm)], ['7', '17'])).
% 1.21/1.45  thf('19', plain, (((sk_A) != (k2_tarski @ sk_B @ sk_C))),
% 1.21/1.45      inference('simpl_trail', [status(thm)], ['6', '18'])).
% 1.21/1.45  thf('20', plain,
% 1.21/1.45      ((((sk_A) = (k1_tarski @ sk_C))
% 1.21/1.45        | ((sk_A) = (k1_tarski @ sk_B))
% 1.21/1.45        | ((sk_A) = (k1_xboole_0))
% 1.21/1.45        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 1.21/1.45      inference('simplify_reflect-', [status(thm)], ['4', '19'])).
% 1.21/1.45  thf('21', plain,
% 1.21/1.45      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 1.21/1.45         <= (~
% 1.21/1.45             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 1.21/1.45      inference('split', [status(esa)], ['2'])).
% 1.21/1.45  thf('22', plain,
% 1.21/1.45      (((((k1_xboole_0) != (k1_xboole_0))
% 1.21/1.45         | ((sk_A) = (k1_xboole_0))
% 1.21/1.45         | ((sk_A) = (k1_tarski @ sk_B))
% 1.21/1.45         | ((sk_A) = (k1_tarski @ sk_C))))
% 1.21/1.45         <= (~
% 1.21/1.45             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 1.21/1.45      inference('sup-', [status(thm)], ['20', '21'])).
% 1.21/1.45  thf('23', plain,
% 1.21/1.45      (((((sk_A) = (k1_tarski @ sk_C))
% 1.21/1.45         | ((sk_A) = (k1_tarski @ sk_B))
% 1.21/1.45         | ((sk_A) = (k1_xboole_0))))
% 1.21/1.45         <= (~
% 1.21/1.45             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 1.21/1.45      inference('simplify', [status(thm)], ['22'])).
% 1.21/1.45  thf(l45_zfmisc_1, axiom,
% 1.21/1.45    (![A:$i,B:$i,C:$i]:
% 1.21/1.45     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 1.21/1.45       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 1.21/1.45            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 1.21/1.45  thf('24', plain,
% 1.21/1.45      (![X48 : $i, X50 : $i, X51 : $i]:
% 1.21/1.45         ((r1_tarski @ X50 @ (k2_tarski @ X48 @ X51))
% 1.21/1.45          | ((X50) != (k1_tarski @ X51)))),
% 1.21/1.45      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 1.21/1.45  thf('25', plain,
% 1.21/1.45      (![X48 : $i, X51 : $i]:
% 1.21/1.45         (r1_tarski @ (k1_tarski @ X51) @ (k2_tarski @ X48 @ X51))),
% 1.21/1.45      inference('simplify', [status(thm)], ['24'])).
% 1.21/1.45  thf(t12_xboole_1, axiom,
% 1.21/1.45    (![A:$i,B:$i]:
% 1.21/1.45     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.21/1.45  thf('26', plain,
% 1.21/1.45      (![X6 : $i, X7 : $i]:
% 1.21/1.45         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.21/1.45      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.21/1.45  thf('27', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 1.21/1.45           = (k2_tarski @ X1 @ X0))),
% 1.21/1.45      inference('sup-', [status(thm)], ['25', '26'])).
% 1.21/1.45  thf(t7_xboole_1, axiom,
% 1.21/1.45    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.21/1.45  thf('28', plain,
% 1.21/1.45      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 1.21/1.45      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.21/1.45  thf('29', plain,
% 1.21/1.45      (![X6 : $i, X7 : $i]:
% 1.21/1.45         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.21/1.45      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.21/1.45  thf('30', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.21/1.45           = (k2_xboole_0 @ X1 @ X0))),
% 1.21/1.45      inference('sup-', [status(thm)], ['28', '29'])).
% 1.21/1.45  thf(t95_xboole_1, axiom,
% 1.21/1.45    (![A:$i,B:$i]:
% 1.21/1.45     ( ( k3_xboole_0 @ A @ B ) =
% 1.21/1.45       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.21/1.45  thf('31', plain,
% 1.21/1.45      (![X16 : $i, X17 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ X16 @ X17)
% 1.21/1.45           = (k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 1.21/1.45              (k2_xboole_0 @ X16 @ X17)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.21/1.45  thf(t91_xboole_1, axiom,
% 1.21/1.45    (![A:$i,B:$i,C:$i]:
% 1.21/1.45     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.21/1.45       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.21/1.45  thf('32', plain,
% 1.21/1.45      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 1.21/1.45           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.21/1.45  thf('33', plain,
% 1.21/1.45      (![X16 : $i, X17 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ X16 @ X17)
% 1.21/1.45           = (k5_xboole_0 @ X16 @ 
% 1.21/1.45              (k5_xboole_0 @ X17 @ (k2_xboole_0 @ X16 @ X17))))),
% 1.21/1.45      inference('demod', [status(thm)], ['31', '32'])).
% 1.21/1.45  thf('34', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.21/1.45           = (k5_xboole_0 @ X1 @ 
% 1.21/1.45              (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))))),
% 1.21/1.45      inference('sup+', [status(thm)], ['30', '33'])).
% 1.21/1.45  thf('35', plain,
% 1.21/1.45      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['9', '10'])).
% 1.21/1.45  thf('36', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 1.21/1.45      inference('demod', [status(thm)], ['8', '11'])).
% 1.21/1.45  thf('37', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.21/1.45           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 1.21/1.45      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.21/1.45  thf(t5_boole, axiom,
% 1.21/1.45    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.21/1.45  thf('38', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.21/1.45      inference('cnf', [status(esa)], [t5_boole])).
% 1.21/1.45  thf('39', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 1.21/1.45      inference('demod', [status(thm)], ['37', '38'])).
% 1.21/1.45  thf('40', plain,
% 1.21/1.45      (![X4 : $i, X5 : $i]:
% 1.21/1.45         ((k4_xboole_0 @ X4 @ X5)
% 1.21/1.45           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.21/1.45  thf('41', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 1.21/1.45           = (k5_xboole_0 @ X0 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['39', '40'])).
% 1.21/1.45  thf('42', plain,
% 1.21/1.45      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['9', '10'])).
% 1.21/1.45  thf('43', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 1.21/1.45           = (k4_xboole_0 @ X0 @ X0))),
% 1.21/1.45      inference('demod', [status(thm)], ['41', '42'])).
% 1.21/1.45  thf('44', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 1.21/1.45           = (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 1.21/1.45      inference('sup+', [status(thm)], ['27', '43'])).
% 1.21/1.45  thf('45', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 1.21/1.45      inference('demod', [status(thm)], ['8', '11'])).
% 1.21/1.45  thf('46', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 1.21/1.45           = (k1_xboole_0))),
% 1.21/1.45      inference('demod', [status(thm)], ['44', '45'])).
% 1.21/1.45  thf('47', plain,
% 1.21/1.45      ((![X0 : $i]:
% 1.21/1.45          (((k4_xboole_0 @ sk_A @ (k2_tarski @ X0 @ sk_C)) = (k1_xboole_0))
% 1.21/1.45           | ((sk_A) = (k1_xboole_0))
% 1.21/1.45           | ((sk_A) = (k1_tarski @ sk_B))))
% 1.21/1.45         <= (~
% 1.21/1.45             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 1.21/1.45      inference('sup+', [status(thm)], ['23', '46'])).
% 1.21/1.45  thf('48', plain,
% 1.21/1.45      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 1.21/1.45         <= (~
% 1.21/1.45             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 1.21/1.45      inference('split', [status(esa)], ['2'])).
% 1.21/1.45  thf('49', plain,
% 1.21/1.45      (((((k1_xboole_0) != (k1_xboole_0))
% 1.21/1.45         | ((sk_A) = (k1_tarski @ sk_B))
% 1.21/1.45         | ((sk_A) = (k1_xboole_0))))
% 1.21/1.45         <= (~
% 1.21/1.45             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 1.21/1.45      inference('sup-', [status(thm)], ['47', '48'])).
% 1.21/1.45  thf('50', plain,
% 1.21/1.45      (((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B))))
% 1.21/1.45         <= (~
% 1.21/1.45             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 1.21/1.45      inference('simplify', [status(thm)], ['49'])).
% 1.21/1.45  thf('51', plain,
% 1.21/1.45      (![X48 : $i, X50 : $i, X51 : $i]:
% 1.21/1.45         ((r1_tarski @ X50 @ (k2_tarski @ X48 @ X51))
% 1.21/1.45          | ((X50) != (k1_tarski @ X48)))),
% 1.21/1.45      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 1.21/1.45  thf('52', plain,
% 1.21/1.45      (![X48 : $i, X51 : $i]:
% 1.21/1.45         (r1_tarski @ (k1_tarski @ X48) @ (k2_tarski @ X48 @ X51))),
% 1.21/1.45      inference('simplify', [status(thm)], ['51'])).
% 1.21/1.45  thf('53', plain,
% 1.21/1.45      (![X6 : $i, X7 : $i]:
% 1.21/1.45         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.21/1.45      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.21/1.45  thf('54', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 1.21/1.45           = (k2_tarski @ X1 @ X0))),
% 1.21/1.45      inference('sup-', [status(thm)], ['52', '53'])).
% 1.21/1.45  thf('55', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 1.21/1.45           = (k4_xboole_0 @ X0 @ X0))),
% 1.21/1.45      inference('demod', [status(thm)], ['41', '42'])).
% 1.21/1.45  thf('56', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 1.21/1.45           = (k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X1)))),
% 1.21/1.45      inference('sup+', [status(thm)], ['54', '55'])).
% 1.21/1.45  thf('57', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 1.21/1.45      inference('demod', [status(thm)], ['8', '11'])).
% 1.21/1.45  thf('58', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 1.21/1.45           = (k1_xboole_0))),
% 1.21/1.45      inference('demod', [status(thm)], ['56', '57'])).
% 1.21/1.45  thf('59', plain,
% 1.21/1.45      ((![X0 : $i]:
% 1.21/1.45          (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ X0)) = (k1_xboole_0))
% 1.21/1.45           | ((sk_A) = (k1_xboole_0))))
% 1.21/1.45         <= (~
% 1.21/1.45             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 1.21/1.45      inference('sup+', [status(thm)], ['50', '58'])).
% 1.21/1.45  thf('60', plain,
% 1.21/1.45      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 1.21/1.45         <= (~
% 1.21/1.45             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 1.21/1.45      inference('split', [status(esa)], ['2'])).
% 1.21/1.45  thf('61', plain,
% 1.21/1.45      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 1.21/1.45         <= (~
% 1.21/1.45             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 1.21/1.45      inference('sup-', [status(thm)], ['59', '60'])).
% 1.21/1.45  thf('62', plain,
% 1.21/1.45      ((((sk_A) = (k1_xboole_0)))
% 1.21/1.45         <= (~
% 1.21/1.45             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 1.21/1.45      inference('simplify', [status(thm)], ['61'])).
% 1.21/1.45  thf('63', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 1.21/1.45      inference('demod', [status(thm)], ['8', '11'])).
% 1.21/1.45  thf('64', plain,
% 1.21/1.45      (![X16 : $i, X17 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ X16 @ X17)
% 1.21/1.45           = (k5_xboole_0 @ X16 @ 
% 1.21/1.45              (k5_xboole_0 @ X17 @ (k2_xboole_0 @ X16 @ X17))))),
% 1.21/1.45      inference('demod', [status(thm)], ['31', '32'])).
% 1.21/1.45  thf('65', plain,
% 1.21/1.45      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['9', '10'])).
% 1.21/1.45  thf('66', plain,
% 1.21/1.45      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 1.21/1.45           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.21/1.45  thf('67', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 1.21/1.45           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 1.21/1.45      inference('sup+', [status(thm)], ['65', '66'])).
% 1.21/1.45  thf('68', plain,
% 1.21/1.45      (![X0 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k2_xboole_0 @ X0 @ X0))
% 1.21/1.45           = (k3_xboole_0 @ X0 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['64', '67'])).
% 1.21/1.45  thf(d10_xboole_0, axiom,
% 1.21/1.45    (![A:$i,B:$i]:
% 1.21/1.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.21/1.45  thf('69', plain,
% 1.21/1.45      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 1.21/1.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.21/1.45  thf('70', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.21/1.45      inference('simplify', [status(thm)], ['69'])).
% 1.21/1.45  thf('71', plain,
% 1.21/1.45      (![X6 : $i, X7 : $i]:
% 1.21/1.45         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.21/1.45      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.21/1.45  thf('72', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.21/1.45      inference('sup-', [status(thm)], ['70', '71'])).
% 1.21/1.45  thf('73', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.21/1.45      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.21/1.45  thf('74', plain,
% 1.21/1.45      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 1.21/1.45      inference('demod', [status(thm)], ['68', '72', '73'])).
% 1.21/1.45  thf('75', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['63', '74'])).
% 1.21/1.45  thf('76', plain,
% 1.21/1.45      (![X4 : $i, X5 : $i]:
% 1.21/1.45         ((k4_xboole_0 @ X4 @ X5)
% 1.21/1.45           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.21/1.45  thf('77', plain,
% 1.21/1.45      (![X0 : $i]:
% 1.21/1.45         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['75', '76'])).
% 1.21/1.45  thf(commutativity_k2_tarski, axiom,
% 1.21/1.45    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.21/1.45  thf('78', plain,
% 1.21/1.45      (![X18 : $i, X19 : $i]:
% 1.21/1.45         ((k2_tarski @ X19 @ X18) = (k2_tarski @ X18 @ X19))),
% 1.21/1.45      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.21/1.45  thf(l51_zfmisc_1, axiom,
% 1.21/1.45    (![A:$i,B:$i]:
% 1.21/1.45     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.21/1.45  thf('79', plain,
% 1.21/1.45      (![X52 : $i, X53 : $i]:
% 1.21/1.45         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 1.21/1.45      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.21/1.45  thf('80', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.21/1.45      inference('sup+', [status(thm)], ['78', '79'])).
% 1.21/1.45  thf('81', plain,
% 1.21/1.45      (![X52 : $i, X53 : $i]:
% 1.21/1.45         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 1.21/1.45      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.21/1.45  thf('82', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.21/1.45      inference('sup+', [status(thm)], ['80', '81'])).
% 1.21/1.45  thf('83', plain,
% 1.21/1.45      (![X16 : $i, X17 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ X16 @ X17)
% 1.21/1.45           = (k5_xboole_0 @ X16 @ 
% 1.21/1.45              (k5_xboole_0 @ X17 @ (k2_xboole_0 @ X16 @ X17))))),
% 1.21/1.45      inference('demod', [status(thm)], ['31', '32'])).
% 1.21/1.45  thf('84', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.21/1.45      inference('cnf', [status(esa)], [t5_boole])).
% 1.21/1.45  thf('85', plain,
% 1.21/1.45      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 1.21/1.45           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.21/1.45  thf('86', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ X1)
% 1.21/1.45           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X1)))),
% 1.21/1.45      inference('sup+', [status(thm)], ['84', '85'])).
% 1.21/1.45  thf('87', plain,
% 1.21/1.45      (![X0 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 1.21/1.45           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['83', '86'])).
% 1.21/1.45  thf(t2_boole, axiom,
% 1.21/1.45    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.21/1.45  thf('88', plain,
% 1.21/1.45      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.45      inference('cnf', [status(esa)], [t2_boole])).
% 1.21/1.45  thf('89', plain,
% 1.21/1.45      (![X0 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.21/1.45      inference('demod', [status(thm)], ['87', '88'])).
% 1.21/1.45  thf('90', plain,
% 1.21/1.45      (![X0 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['82', '89'])).
% 1.21/1.45  thf('91', plain,
% 1.21/1.45      (![X16 : $i, X17 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ X16 @ X17)
% 1.21/1.45           = (k5_xboole_0 @ X16 @ 
% 1.21/1.45              (k5_xboole_0 @ X17 @ (k2_xboole_0 @ X16 @ X17))))),
% 1.21/1.45      inference('demod', [status(thm)], ['31', '32'])).
% 1.21/1.45  thf('92', plain,
% 1.21/1.45      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 1.21/1.45           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.21/1.45  thf('93', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0)
% 1.21/1.45           = (k5_xboole_0 @ X2 @ 
% 1.21/1.45              (k5_xboole_0 @ X1 @ 
% 1.21/1.45               (k5_xboole_0 @ X0 @ (k2_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0)))))),
% 1.21/1.45      inference('sup+', [status(thm)], ['91', '92'])).
% 1.21/1.45  thf('94', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ 
% 1.21/1.45           (k5_xboole_0 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X1)) @ X0)
% 1.21/1.45           = (k5_xboole_0 @ X1 @ 
% 1.21/1.45              (k5_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ 
% 1.21/1.45               (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))))),
% 1.21/1.45      inference('sup+', [status(thm)], ['90', '93'])).
% 1.21/1.45  thf('95', plain,
% 1.21/1.45      (![X0 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['82', '89'])).
% 1.21/1.45  thf('96', plain,
% 1.21/1.45      (![X0 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['82', '89'])).
% 1.21/1.45  thf('97', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.21/1.45      inference('cnf', [status(esa)], [t5_boole])).
% 1.21/1.45  thf('98', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 1.21/1.45           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 1.21/1.45      inference('demod', [status(thm)], ['94', '95', '96', '97'])).
% 1.21/1.45  thf('99', plain,
% 1.21/1.45      (![X0 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['82', '89'])).
% 1.21/1.45  thf('100', plain,
% 1.21/1.45      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.21/1.45      inference('demod', [status(thm)], ['98', '99'])).
% 1.21/1.45  thf('101', plain,
% 1.21/1.45      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.21/1.45      inference('demod', [status(thm)], ['77', '100'])).
% 1.21/1.45  thf('102', plain,
% 1.21/1.45      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.21/1.45         <= (~
% 1.21/1.45             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 1.21/1.45      inference('demod', [status(thm)], ['3', '62', '101'])).
% 1.21/1.45  thf('103', plain,
% 1.21/1.45      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 1.21/1.45      inference('simplify', [status(thm)], ['102'])).
% 1.21/1.45  thf('104', plain,
% 1.21/1.45      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 1.21/1.45      inference('sat_resolution*', [status(thm)], ['103'])).
% 1.21/1.45  thf('105', plain,
% 1.21/1.45      (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))),
% 1.21/1.45      inference('simpl_trail', [status(thm)], ['1', '104'])).
% 1.21/1.45  thf('106', plain,
% 1.21/1.45      (![X4 : $i, X5 : $i]:
% 1.21/1.45         ((k4_xboole_0 @ X4 @ X5)
% 1.21/1.45           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.21/1.45  thf('107', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 1.21/1.45           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 1.21/1.45      inference('sup+', [status(thm)], ['65', '66'])).
% 1.21/1.45  thf('108', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 1.21/1.45      inference('demod', [status(thm)], ['8', '11'])).
% 1.21/1.45  thf('109', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 1.21/1.45      inference('demod', [status(thm)], ['8', '11'])).
% 1.21/1.45  thf('110', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X1 @ X1) = (k4_xboole_0 @ X0 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['108', '109'])).
% 1.21/1.45  thf('111', plain,
% 1.21/1.45      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 1.21/1.45      inference('demod', [status(thm)], ['68', '72', '73'])).
% 1.21/1.45  thf('112', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 1.21/1.45      inference('sup+', [status(thm)], ['110', '111'])).
% 1.21/1.45  thf('113', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 1.21/1.45      inference('demod', [status(thm)], ['107', '112'])).
% 1.21/1.45  thf('114', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ X1 @ X0)
% 1.21/1.45           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.21/1.45      inference('sup+', [status(thm)], ['106', '113'])).
% 1.21/1.45  thf('115', plain,
% 1.21/1.45      (((k3_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C))
% 1.21/1.45         = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['105', '114'])).
% 1.21/1.45  thf('116', plain,
% 1.21/1.45      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['9', '10'])).
% 1.21/1.45  thf('117', plain,
% 1.21/1.45      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 1.21/1.45           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.21/1.45  thf('118', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 1.21/1.45           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 1.21/1.45      inference('sup+', [status(thm)], ['116', '117'])).
% 1.21/1.45  thf('119', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 1.21/1.45      inference('demod', [status(thm)], ['8', '11'])).
% 1.21/1.45  thf('120', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k1_xboole_0)
% 1.21/1.45           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 1.21/1.45      inference('demod', [status(thm)], ['118', '119'])).
% 1.21/1.45  thf('121', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 1.21/1.45      inference('demod', [status(thm)], ['107', '112'])).
% 1.21/1.45  thf('122', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 1.21/1.45           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['120', '121'])).
% 1.21/1.45  thf('123', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.21/1.45      inference('cnf', [status(esa)], [t5_boole])).
% 1.21/1.45  thf('124', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 1.21/1.45      inference('demod', [status(thm)], ['122', '123'])).
% 1.21/1.45  thf('125', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 1.21/1.45      inference('demod', [status(thm)], ['107', '112'])).
% 1.21/1.45  thf('126', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['124', '125'])).
% 1.21/1.45  thf('127', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['63', '74'])).
% 1.21/1.45  thf('128', plain,
% 1.21/1.45      (((k3_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (sk_A))),
% 1.21/1.45      inference('demod', [status(thm)], ['115', '126', '127'])).
% 1.21/1.45  thf('129', plain,
% 1.21/1.45      (![X16 : $i, X17 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ X16 @ X17)
% 1.21/1.45           = (k5_xboole_0 @ X16 @ 
% 1.21/1.45              (k5_xboole_0 @ X17 @ (k2_xboole_0 @ X16 @ X17))))),
% 1.21/1.45      inference('demod', [status(thm)], ['31', '32'])).
% 1.21/1.45  thf('130', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k1_xboole_0)
% 1.21/1.45           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 1.21/1.45      inference('demod', [status(thm)], ['118', '119'])).
% 1.21/1.45  thf('131', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k1_xboole_0)
% 1.21/1.45           = (k5_xboole_0 @ X1 @ 
% 1.21/1.45              (k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 1.21/1.45               (k3_xboole_0 @ X1 @ X0))))),
% 1.21/1.45      inference('sup+', [status(thm)], ['129', '130'])).
% 1.21/1.45  thf('132', plain,
% 1.21/1.45      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 1.21/1.45           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.21/1.45  thf('133', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k1_xboole_0)
% 1.21/1.45           = (k5_xboole_0 @ X1 @ 
% 1.21/1.45              (k5_xboole_0 @ X0 @ 
% 1.21/1.45               (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))))),
% 1.21/1.45      inference('demod', [status(thm)], ['131', '132'])).
% 1.21/1.45  thf('134', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['124', '125'])).
% 1.21/1.45  thf('135', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k1_xboole_0)
% 1.21/1.45           = (k5_xboole_0 @ X1 @ 
% 1.21/1.45              (k5_xboole_0 @ X0 @ 
% 1.21/1.45               (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))))),
% 1.21/1.45      inference('demod', [status(thm)], ['133', '134'])).
% 1.21/1.45  thf('136', plain,
% 1.21/1.45      (((k1_xboole_0)
% 1.21/1.45         = (k5_xboole_0 @ sk_A @ 
% 1.21/1.45            (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ 
% 1.21/1.45             (k5_xboole_0 @ sk_A @ 
% 1.21/1.45              (k2_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C))))))),
% 1.21/1.45      inference('sup+', [status(thm)], ['128', '135'])).
% 1.21/1.45  thf('137', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.21/1.45      inference('sup+', [status(thm)], ['80', '81'])).
% 1.21/1.45  thf('138', plain,
% 1.21/1.45      (![X16 : $i, X17 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ X16 @ X17)
% 1.21/1.45           = (k5_xboole_0 @ X16 @ 
% 1.21/1.45              (k5_xboole_0 @ X17 @ (k2_xboole_0 @ X16 @ X17))))),
% 1.21/1.45      inference('demod', [status(thm)], ['31', '32'])).
% 1.21/1.45  thf('139', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ X0 @ X1)
% 1.21/1.45           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.21/1.45      inference('sup+', [status(thm)], ['137', '138'])).
% 1.21/1.45  thf('140', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 1.21/1.45      inference('demod', [status(thm)], ['107', '112'])).
% 1.21/1.45  thf('141', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 1.21/1.45           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.21/1.45      inference('sup+', [status(thm)], ['139', '140'])).
% 1.21/1.45  thf('142', plain,
% 1.21/1.45      (![X4 : $i, X5 : $i]:
% 1.21/1.45         ((k4_xboole_0 @ X4 @ X5)
% 1.21/1.45           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.21/1.45  thf('143', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 1.21/1.45           = (k4_xboole_0 @ X1 @ X0))),
% 1.21/1.45      inference('demod', [status(thm)], ['141', '142'])).
% 1.21/1.45  thf('144', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ X1 @ X0)
% 1.21/1.45           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.21/1.45      inference('sup+', [status(thm)], ['106', '113'])).
% 1.21/1.45  thf('145', plain,
% 1.21/1.45      (((k1_xboole_0)
% 1.21/1.45         = (k5_xboole_0 @ sk_A @ 
% 1.21/1.45            (k3_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ sk_A)))),
% 1.21/1.45      inference('demod', [status(thm)], ['136', '143', '144'])).
% 1.21/1.45  thf('146', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 1.21/1.45      inference('demod', [status(thm)], ['122', '123'])).
% 1.21/1.45  thf('147', plain,
% 1.21/1.45      (((k5_xboole_0 @ (k3_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ sk_A) @ 
% 1.21/1.45         k1_xboole_0) = (sk_A))),
% 1.21/1.45      inference('sup+', [status(thm)], ['145', '146'])).
% 1.21/1.45  thf('148', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['124', '125'])).
% 1.21/1.45  thf('149', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['63', '74'])).
% 1.21/1.45  thf('150', plain,
% 1.21/1.45      (((k3_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ sk_A) = (sk_A))),
% 1.21/1.45      inference('demod', [status(thm)], ['147', '148', '149'])).
% 1.21/1.45  thf('151', plain,
% 1.21/1.45      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['9', '10'])).
% 1.21/1.45  thf('152', plain,
% 1.21/1.45      (![X4 : $i, X5 : $i]:
% 1.21/1.45         ((k4_xboole_0 @ X4 @ X5)
% 1.21/1.45           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.21/1.45  thf('153', plain,
% 1.21/1.45      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 1.21/1.45           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.21/1.45  thf('154', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 1.21/1.45           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 1.21/1.45      inference('sup+', [status(thm)], ['152', '153'])).
% 1.21/1.45  thf('155', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.21/1.45           = (k5_xboole_0 @ X1 @ 
% 1.21/1.45              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 1.21/1.45      inference('sup+', [status(thm)], ['151', '154'])).
% 1.21/1.45  thf('156', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 1.21/1.45      inference('demod', [status(thm)], ['8', '11'])).
% 1.21/1.45  thf('157', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.21/1.45           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 1.21/1.45      inference('demod', [status(thm)], ['155', '156'])).
% 1.21/1.45  thf('158', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.21/1.45      inference('cnf', [status(esa)], [t5_boole])).
% 1.21/1.45  thf('159', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.21/1.45           = (X1))),
% 1.21/1.45      inference('demod', [status(thm)], ['157', '158'])).
% 1.21/1.45  thf('160', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['124', '125'])).
% 1.21/1.45  thf('161', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.21/1.45           = (X1))),
% 1.21/1.45      inference('demod', [status(thm)], ['159', '160'])).
% 1.21/1.45  thf('162', plain,
% 1.21/1.45      (((k5_xboole_0 @ sk_A @ (k4_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ sk_A))
% 1.21/1.45         = (k2_tarski @ sk_B @ sk_C))),
% 1.21/1.45      inference('sup+', [status(thm)], ['150', '161'])).
% 1.21/1.45  thf('163', plain,
% 1.21/1.45      (![X16 : $i, X17 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ X16 @ X17)
% 1.21/1.45           = (k5_xboole_0 @ X16 @ 
% 1.21/1.45              (k5_xboole_0 @ X17 @ (k2_xboole_0 @ X16 @ X17))))),
% 1.21/1.45      inference('demod', [status(thm)], ['31', '32'])).
% 1.21/1.45  thf('164', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 1.21/1.45           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 1.21/1.45      inference('sup+', [status(thm)], ['65', '66'])).
% 1.21/1.45  thf('165', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ 
% 1.21/1.45           (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 1.21/1.45           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.21/1.45      inference('sup+', [status(thm)], ['163', '164'])).
% 1.21/1.45  thf('166', plain,
% 1.21/1.45      (![X4 : $i, X5 : $i]:
% 1.21/1.45         ((k4_xboole_0 @ X4 @ X5)
% 1.21/1.45           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.21/1.45  thf('167', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ 
% 1.21/1.45           (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 1.21/1.45           = (k4_xboole_0 @ X1 @ X0))),
% 1.21/1.45      inference('demod', [status(thm)], ['165', '166'])).
% 1.21/1.45  thf('168', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 1.21/1.45      inference('sup+', [status(thm)], ['110', '111'])).
% 1.21/1.45  thf('169', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.21/1.45           = (k4_xboole_0 @ X1 @ X0))),
% 1.21/1.45      inference('demod', [status(thm)], ['167', '168'])).
% 1.21/1.45  thf('170', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 1.21/1.45      inference('demod', [status(thm)], ['107', '112'])).
% 1.21/1.45  thf('171', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k2_xboole_0 @ X1 @ X0)
% 1.21/1.45           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.21/1.45      inference('sup+', [status(thm)], ['169', '170'])).
% 1.21/1.45  thf('172', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.21/1.45      inference('sup+', [status(thm)], ['80', '81'])).
% 1.21/1.45  thf('173', plain,
% 1.21/1.45      (((k2_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C))
% 1.21/1.45         = (k2_tarski @ sk_B @ sk_C))),
% 1.21/1.45      inference('demod', [status(thm)], ['162', '171', '172'])).
% 1.21/1.45  thf('174', plain,
% 1.21/1.45      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 1.21/1.45      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.21/1.45  thf('175', plain, ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))),
% 1.21/1.45      inference('sup+', [status(thm)], ['173', '174'])).
% 1.21/1.45  thf('176', plain,
% 1.21/1.45      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.21/1.45         (((X50) = (k2_tarski @ X48 @ X49))
% 1.21/1.45          | ((X50) = (k1_tarski @ X49))
% 1.21/1.45          | ((X50) = (k1_tarski @ X48))
% 1.21/1.45          | ((X50) = (k1_xboole_0))
% 1.21/1.45          | ~ (r1_tarski @ X50 @ (k2_tarski @ X48 @ X49)))),
% 1.21/1.45      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 1.21/1.45  thf('177', plain,
% 1.21/1.45      ((((sk_A) = (k1_xboole_0))
% 1.21/1.45        | ((sk_A) = (k1_tarski @ sk_B))
% 1.21/1.45        | ((sk_A) = (k1_tarski @ sk_C))
% 1.21/1.45        | ((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 1.21/1.45      inference('sup-', [status(thm)], ['175', '176'])).
% 1.21/1.45  thf('178', plain, (((sk_A) != (k2_tarski @ sk_B @ sk_C))),
% 1.21/1.45      inference('simpl_trail', [status(thm)], ['6', '18'])).
% 1.21/1.45  thf('179', plain,
% 1.21/1.45      ((((sk_A) != (k1_tarski @ sk_C))
% 1.21/1.45        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 1.21/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.45  thf('180', plain,
% 1.21/1.45      ((((sk_A) != (k1_tarski @ sk_C))) <= (~ (((sk_A) = (k1_tarski @ sk_C))))),
% 1.21/1.45      inference('split', [status(esa)], ['179'])).
% 1.21/1.45  thf('181', plain,
% 1.21/1.45      (~ (((sk_A) = (k1_tarski @ sk_C))) | 
% 1.21/1.45       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 1.21/1.45      inference('split', [status(esa)], ['179'])).
% 1.21/1.45  thf('182', plain, (~ (((sk_A) = (k1_tarski @ sk_C)))),
% 1.21/1.45      inference('sat_resolution*', [status(thm)], ['103', '181'])).
% 1.21/1.45  thf('183', plain, (((sk_A) != (k1_tarski @ sk_C))),
% 1.21/1.45      inference('simpl_trail', [status(thm)], ['180', '182'])).
% 1.21/1.45  thf('184', plain,
% 1.21/1.45      ((((sk_A) != (k1_tarski @ sk_B))
% 1.21/1.45        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 1.21/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.45  thf('185', plain,
% 1.21/1.45      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 1.21/1.45      inference('split', [status(esa)], ['184'])).
% 1.21/1.45  thf('186', plain,
% 1.21/1.45      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 1.21/1.45       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 1.21/1.45      inference('split', [status(esa)], ['184'])).
% 1.21/1.45  thf('187', plain, (~ (((sk_A) = (k1_tarski @ sk_B)))),
% 1.21/1.45      inference('sat_resolution*', [status(thm)], ['103', '186'])).
% 1.21/1.45  thf('188', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 1.21/1.45      inference('simpl_trail', [status(thm)], ['185', '187'])).
% 1.21/1.45  thf('189', plain,
% 1.21/1.45      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 1.21/1.45      inference('split', [status(esa)], ['2'])).
% 1.21/1.45  thf('190', plain,
% 1.21/1.45      (~ (((sk_A) = (k1_xboole_0))) | 
% 1.21/1.45       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 1.21/1.45      inference('split', [status(esa)], ['2'])).
% 1.21/1.45  thf('191', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 1.21/1.45      inference('sat_resolution*', [status(thm)], ['103', '190'])).
% 1.21/1.45  thf('192', plain, (((sk_A) != (k1_xboole_0))),
% 1.21/1.45      inference('simpl_trail', [status(thm)], ['189', '191'])).
% 1.21/1.45  thf('193', plain, ($false),
% 1.21/1.45      inference('simplify_reflect-', [status(thm)],
% 1.21/1.45                ['177', '178', '183', '188', '192'])).
% 1.21/1.45  
% 1.21/1.45  % SZS output end Refutation
% 1.21/1.45  
% 1.31/1.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

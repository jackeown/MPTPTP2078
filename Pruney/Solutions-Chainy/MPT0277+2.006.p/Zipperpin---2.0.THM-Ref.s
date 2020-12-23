%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xPgLcudJnC

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:41 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 672 expanded)
%              Number of leaves         :   25 ( 196 expanded)
%              Depth                    :   26
%              Number of atoms          : 1154 (7279 expanded)
%              Number of equality atoms :  185 (1279 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ X20 )
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
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( r1_tarski @ X30 @ ( k2_tarski @ X28 @ X31 ) )
      | ( X30
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('25',plain,(
    ! [X28: $i,X31: $i] :
      ( r1_tarski @ ( k1_tarski @ X31 ) @ ( k2_tarski @ X28 @ X31 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('31',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ X0 @ sk_C ) )
          = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ( sk_A
          = ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','32'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('35',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( r1_tarski @ X30 @ ( k2_tarski @ X28 @ X31 ) )
      | ( X30
       != ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('38',plain,(
    ! [X28: $i,X31: $i] :
      ( r1_tarski @ ( k1_tarski @ X28 ) @ ( k2_tarski @ X28 @ X31 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('44',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ X0 ) )
          = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','45'])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('48',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('52',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('56',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('57',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('58',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('60',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('64',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['64'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('66',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k2_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['63','67'])).

thf('69',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','70'])).

thf('72',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','49','71'])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['73'])).

thf('75',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','74'])).

thf('76',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('77',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('82',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('87',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('88',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('89',plain,(
    r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X30
        = ( k2_tarski @ X28 @ X29 ) )
      | ( X30
        = ( k1_tarski @ X29 ) )
      | ( X30
        = ( k1_tarski @ X28 ) )
      | ( X30 = k1_xboole_0 )
      | ~ ( r1_tarski @ X30 @ ( k2_tarski @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('91',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    sk_A
 != ( k2_tarski @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['6','18'])).

thf('93',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
   <= ( sk_A
     != ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['93'])).

thf('95',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['93'])).

thf('96',plain,(
    sk_A
 != ( k1_tarski @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['73','95'])).

thf('97',plain,(
    sk_A
 != ( k1_tarski @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['94','96'])).

thf('98',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['98'])).

thf('100',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['98'])).

thf('101',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['73','100'])).

thf('102',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['99','101'])).

thf('103',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('104',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('105',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['73','104'])).

thf('106',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['103','105'])).

thf('107',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['91','92','97','102','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xPgLcudJnC
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.85/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.85/1.04  % Solved by: fo/fo7.sh
% 0.85/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.04  % done 1123 iterations in 0.588s
% 0.85/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.85/1.04  % SZS output start Refutation
% 0.85/1.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.85/1.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.85/1.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.85/1.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.85/1.04  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.85/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.85/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.04  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.85/1.04  thf(sk_C_type, type, sk_C: $i).
% 0.85/1.04  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.85/1.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.85/1.04  thf(t75_zfmisc_1, conjecture,
% 0.85/1.04    (![A:$i,B:$i,C:$i]:
% 0.85/1.04     ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.85/1.04       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.85/1.04            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.85/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.04    (~( ![A:$i,B:$i,C:$i]:
% 0.85/1.04        ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.85/1.04          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.85/1.04               ( ( A ) != ( k1_tarski @ C ) ) & 
% 0.85/1.04               ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ) )),
% 0.85/1.04    inference('cnf.neg', [status(esa)], [t75_zfmisc_1])).
% 0.85/1.04  thf('0', plain,
% 0.85/1.04      ((((sk_A) = (k2_tarski @ sk_B @ sk_C))
% 0.85/1.04        | ((sk_A) = (k1_tarski @ sk_C))
% 0.85/1.04        | ((sk_A) = (k1_tarski @ sk_B))
% 0.85/1.04        | ((sk_A) = (k1_xboole_0))
% 0.85/1.04        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('1', plain,
% 0.85/1.04      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))
% 0.85/1.04         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.85/1.04      inference('split', [status(esa)], ['0'])).
% 0.85/1.04  thf('2', plain,
% 0.85/1.04      ((((sk_A) != (k1_xboole_0))
% 0.85/1.04        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('3', plain,
% 0.85/1.04      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.85/1.04      inference('split', [status(esa)], ['2'])).
% 0.85/1.04  thf('4', plain,
% 0.85/1.04      ((((sk_A) = (k2_tarski @ sk_B @ sk_C))
% 0.85/1.04        | ((sk_A) = (k1_tarski @ sk_C))
% 0.85/1.04        | ((sk_A) = (k1_tarski @ sk_B))
% 0.85/1.04        | ((sk_A) = (k1_xboole_0))
% 0.85/1.04        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('5', plain,
% 0.85/1.04      ((((sk_A) != (k2_tarski @ sk_B @ sk_C))
% 0.85/1.04        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('6', plain,
% 0.85/1.04      ((((sk_A) != (k2_tarski @ sk_B @ sk_C)))
% 0.85/1.04         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.85/1.04      inference('split', [status(esa)], ['5'])).
% 0.85/1.04  thf('7', plain,
% 0.85/1.04      (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) | 
% 0.85/1.04       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.85/1.04      inference('split', [status(esa)], ['5'])).
% 0.85/1.04  thf(t92_xboole_1, axiom,
% 0.85/1.04    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.85/1.04  thf('8', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.85/1.04      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.85/1.04  thf(idempotence_k3_xboole_0, axiom,
% 0.85/1.04    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.85/1.04  thf('9', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.85/1.04      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.85/1.04  thf(t100_xboole_1, axiom,
% 0.85/1.04    (![A:$i,B:$i]:
% 0.85/1.04     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.85/1.04  thf('10', plain,
% 0.85/1.04      (![X6 : $i, X7 : $i]:
% 0.85/1.04         ((k4_xboole_0 @ X6 @ X7)
% 0.85/1.04           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.85/1.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.04  thf('11', plain,
% 0.85/1.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.85/1.04      inference('sup+', [status(thm)], ['9', '10'])).
% 0.85/1.04  thf('12', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.85/1.04      inference('demod', [status(thm)], ['8', '11'])).
% 0.85/1.04  thf('13', plain,
% 0.85/1.04      ((((sk_A) = (k2_tarski @ sk_B @ sk_C)))
% 0.85/1.04         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.85/1.04      inference('split', [status(esa)], ['0'])).
% 0.85/1.04  thf('14', plain,
% 0.85/1.04      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.85/1.04      inference('split', [status(esa)], ['2'])).
% 0.85/1.04  thf('15', plain,
% 0.85/1.04      ((((k4_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0)))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.85/1.04             (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.85/1.04      inference('sup-', [status(thm)], ['13', '14'])).
% 0.85/1.04  thf('16', plain,
% 0.85/1.04      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.85/1.04             (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.85/1.04      inference('sup-', [status(thm)], ['12', '15'])).
% 0.85/1.04  thf('17', plain,
% 0.85/1.04      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.85/1.04       ~ (((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 0.85/1.04      inference('simplify', [status(thm)], ['16'])).
% 0.85/1.04  thf('18', plain, (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 0.85/1.04      inference('sat_resolution*', [status(thm)], ['7', '17'])).
% 0.85/1.04  thf('19', plain, (((sk_A) != (k2_tarski @ sk_B @ sk_C))),
% 0.85/1.04      inference('simpl_trail', [status(thm)], ['6', '18'])).
% 0.85/1.04  thf('20', plain,
% 0.85/1.04      ((((sk_A) = (k1_tarski @ sk_C))
% 0.85/1.04        | ((sk_A) = (k1_tarski @ sk_B))
% 0.85/1.04        | ((sk_A) = (k1_xboole_0))
% 0.85/1.04        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.85/1.04      inference('simplify_reflect-', [status(thm)], ['4', '19'])).
% 0.85/1.04  thf('21', plain,
% 0.85/1.04      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.85/1.04      inference('split', [status(esa)], ['2'])).
% 0.85/1.04  thf('22', plain,
% 0.85/1.04      (((((k1_xboole_0) != (k1_xboole_0))
% 0.85/1.04         | ((sk_A) = (k1_xboole_0))
% 0.85/1.04         | ((sk_A) = (k1_tarski @ sk_B))
% 0.85/1.04         | ((sk_A) = (k1_tarski @ sk_C))))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.85/1.04      inference('sup-', [status(thm)], ['20', '21'])).
% 0.85/1.04  thf('23', plain,
% 0.85/1.04      (((((sk_A) = (k1_tarski @ sk_C))
% 0.85/1.04         | ((sk_A) = (k1_tarski @ sk_B))
% 0.85/1.04         | ((sk_A) = (k1_xboole_0))))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.85/1.04      inference('simplify', [status(thm)], ['22'])).
% 0.85/1.04  thf(l45_zfmisc_1, axiom,
% 0.85/1.04    (![A:$i,B:$i,C:$i]:
% 0.85/1.04     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.85/1.04       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.85/1.04            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.85/1.04  thf('24', plain,
% 0.85/1.04      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.85/1.04         ((r1_tarski @ X30 @ (k2_tarski @ X28 @ X31))
% 0.85/1.04          | ((X30) != (k1_tarski @ X31)))),
% 0.85/1.04      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.85/1.04  thf('25', plain,
% 0.85/1.04      (![X28 : $i, X31 : $i]:
% 0.85/1.04         (r1_tarski @ (k1_tarski @ X31) @ (k2_tarski @ X28 @ X31))),
% 0.85/1.04      inference('simplify', [status(thm)], ['24'])).
% 0.85/1.04  thf(t28_xboole_1, axiom,
% 0.85/1.04    (![A:$i,B:$i]:
% 0.85/1.04     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.85/1.04  thf('26', plain,
% 0.85/1.04      (![X11 : $i, X12 : $i]:
% 0.85/1.04         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.85/1.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.85/1.04  thf('27', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.85/1.04           = (k1_tarski @ X0))),
% 0.85/1.04      inference('sup-', [status(thm)], ['25', '26'])).
% 0.85/1.04  thf('28', plain,
% 0.85/1.04      (![X6 : $i, X7 : $i]:
% 0.85/1.04         ((k4_xboole_0 @ X6 @ X7)
% 0.85/1.04           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.85/1.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.04  thf('29', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.85/1.04           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.85/1.04      inference('sup+', [status(thm)], ['27', '28'])).
% 0.85/1.04  thf('30', plain,
% 0.85/1.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.85/1.04      inference('sup+', [status(thm)], ['9', '10'])).
% 0.85/1.04  thf('31', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.85/1.04      inference('demod', [status(thm)], ['8', '11'])).
% 0.85/1.04  thf('32', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.85/1.04           = (k1_xboole_0))),
% 0.85/1.04      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.85/1.04  thf('33', plain,
% 0.85/1.04      ((![X0 : $i]:
% 0.85/1.04          (((k4_xboole_0 @ sk_A @ (k2_tarski @ X0 @ sk_C)) = (k1_xboole_0))
% 0.85/1.04           | ((sk_A) = (k1_xboole_0))
% 0.85/1.04           | ((sk_A) = (k1_tarski @ sk_B))))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.85/1.04      inference('sup+', [status(thm)], ['23', '32'])).
% 0.85/1.04  thf('34', plain,
% 0.85/1.04      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.85/1.04      inference('split', [status(esa)], ['2'])).
% 0.85/1.04  thf('35', plain,
% 0.85/1.04      (((((k1_xboole_0) != (k1_xboole_0))
% 0.85/1.04         | ((sk_A) = (k1_tarski @ sk_B))
% 0.85/1.04         | ((sk_A) = (k1_xboole_0))))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.85/1.04      inference('sup-', [status(thm)], ['33', '34'])).
% 0.85/1.04  thf('36', plain,
% 0.85/1.04      (((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B))))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.85/1.04      inference('simplify', [status(thm)], ['35'])).
% 0.85/1.04  thf('37', plain,
% 0.85/1.04      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.85/1.04         ((r1_tarski @ X30 @ (k2_tarski @ X28 @ X31))
% 0.85/1.04          | ((X30) != (k1_tarski @ X28)))),
% 0.85/1.04      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.85/1.04  thf('38', plain,
% 0.85/1.04      (![X28 : $i, X31 : $i]:
% 0.85/1.04         (r1_tarski @ (k1_tarski @ X28) @ (k2_tarski @ X28 @ X31))),
% 0.85/1.04      inference('simplify', [status(thm)], ['37'])).
% 0.85/1.04  thf('39', plain,
% 0.85/1.04      (![X11 : $i, X12 : $i]:
% 0.85/1.04         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.85/1.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.85/1.04  thf('40', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.85/1.04           = (k1_tarski @ X1))),
% 0.85/1.04      inference('sup-', [status(thm)], ['38', '39'])).
% 0.85/1.04  thf('41', plain,
% 0.85/1.04      (![X6 : $i, X7 : $i]:
% 0.85/1.04         ((k4_xboole_0 @ X6 @ X7)
% 0.85/1.04           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.85/1.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.04  thf('42', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.85/1.04           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.85/1.04      inference('sup+', [status(thm)], ['40', '41'])).
% 0.85/1.04  thf('43', plain,
% 0.85/1.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.85/1.04      inference('sup+', [status(thm)], ['9', '10'])).
% 0.85/1.04  thf('44', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.85/1.04      inference('demod', [status(thm)], ['8', '11'])).
% 0.85/1.04  thf('45', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.85/1.04           = (k1_xboole_0))),
% 0.85/1.04      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.85/1.04  thf('46', plain,
% 0.85/1.04      ((![X0 : $i]:
% 0.85/1.04          (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ X0)) = (k1_xboole_0))
% 0.85/1.04           | ((sk_A) = (k1_xboole_0))))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.85/1.04      inference('sup+', [status(thm)], ['36', '45'])).
% 0.85/1.04  thf('47', plain,
% 0.85/1.04      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.85/1.04      inference('split', [status(esa)], ['2'])).
% 0.85/1.04  thf('48', plain,
% 0.85/1.04      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.85/1.04      inference('sup-', [status(thm)], ['46', '47'])).
% 0.85/1.04  thf('49', plain,
% 0.85/1.04      ((((sk_A) = (k1_xboole_0)))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.85/1.04      inference('simplify', [status(thm)], ['48'])).
% 0.85/1.04  thf('50', plain,
% 0.85/1.04      (![X6 : $i, X7 : $i]:
% 0.85/1.04         ((k4_xboole_0 @ X6 @ X7)
% 0.85/1.04           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.85/1.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.04  thf(commutativity_k5_xboole_0, axiom,
% 0.85/1.04    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.85/1.04  thf('51', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.85/1.04      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.04  thf(t5_boole, axiom,
% 0.85/1.04    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.85/1.04  thf('52', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.85/1.04      inference('cnf', [status(esa)], [t5_boole])).
% 0.85/1.04  thf('53', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.85/1.04      inference('sup+', [status(thm)], ['51', '52'])).
% 0.85/1.04  thf('54', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.85/1.04      inference('sup+', [status(thm)], ['50', '53'])).
% 0.85/1.04  thf('55', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.85/1.04      inference('sup+', [status(thm)], ['51', '52'])).
% 0.85/1.04  thf(t94_xboole_1, axiom,
% 0.85/1.04    (![A:$i,B:$i]:
% 0.85/1.04     ( ( k2_xboole_0 @ A @ B ) =
% 0.85/1.04       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.85/1.04  thf('56', plain,
% 0.85/1.04      (![X21 : $i, X22 : $i]:
% 0.85/1.04         ((k2_xboole_0 @ X21 @ X22)
% 0.85/1.04           = (k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ 
% 0.85/1.04              (k3_xboole_0 @ X21 @ X22)))),
% 0.85/1.04      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.85/1.04  thf(t91_xboole_1, axiom,
% 0.85/1.04    (![A:$i,B:$i,C:$i]:
% 0.85/1.04     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.85/1.04       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.85/1.04  thf('57', plain,
% 0.85/1.04      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.85/1.04         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.85/1.04           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.85/1.04      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.85/1.04  thf('58', plain,
% 0.85/1.04      (![X21 : $i, X22 : $i]:
% 0.85/1.04         ((k2_xboole_0 @ X21 @ X22)
% 0.85/1.04           = (k5_xboole_0 @ X21 @ 
% 0.85/1.04              (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X22))))),
% 0.85/1.04      inference('demod', [status(thm)], ['56', '57'])).
% 0.85/1.04  thf('59', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.85/1.04           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.85/1.04      inference('sup+', [status(thm)], ['55', '58'])).
% 0.85/1.04  thf(t2_boole, axiom,
% 0.85/1.04    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.85/1.04  thf('60', plain,
% 0.85/1.04      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.85/1.04      inference('cnf', [status(esa)], [t2_boole])).
% 0.85/1.04  thf('61', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.85/1.04      inference('demod', [status(thm)], ['59', '60'])).
% 0.85/1.04  thf('62', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.85/1.04      inference('cnf', [status(esa)], [t5_boole])).
% 0.85/1.04  thf('63', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.85/1.04      inference('sup+', [status(thm)], ['61', '62'])).
% 0.85/1.04  thf(d10_xboole_0, axiom,
% 0.85/1.04    (![A:$i,B:$i]:
% 0.85/1.04     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.85/1.04  thf('64', plain,
% 0.85/1.04      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.85/1.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.85/1.04  thf('65', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.85/1.04      inference('simplify', [status(thm)], ['64'])).
% 0.85/1.04  thf(t10_xboole_1, axiom,
% 0.85/1.04    (![A:$i,B:$i,C:$i]:
% 0.85/1.04     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.85/1.04  thf('66', plain,
% 0.85/1.04      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.85/1.04         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ X8 @ (k2_xboole_0 @ X10 @ X9)))),
% 0.85/1.04      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.85/1.04  thf('67', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.85/1.04      inference('sup-', [status(thm)], ['65', '66'])).
% 0.85/1.04  thf('68', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.85/1.04      inference('sup+', [status(thm)], ['63', '67'])).
% 0.85/1.04  thf('69', plain,
% 0.85/1.04      (![X11 : $i, X12 : $i]:
% 0.85/1.04         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.85/1.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.85/1.04  thf('70', plain,
% 0.85/1.04      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.85/1.04      inference('sup-', [status(thm)], ['68', '69'])).
% 0.85/1.04  thf('71', plain,
% 0.85/1.04      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.85/1.04      inference('demod', [status(thm)], ['54', '70'])).
% 0.85/1.04  thf('72', plain,
% 0.85/1.04      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.85/1.04      inference('demod', [status(thm)], ['3', '49', '71'])).
% 0.85/1.04  thf('73', plain,
% 0.85/1.04      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.85/1.04      inference('simplify', [status(thm)], ['72'])).
% 0.85/1.04  thf('74', plain,
% 0.85/1.04      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.85/1.04      inference('sat_resolution*', [status(thm)], ['73'])).
% 0.85/1.04  thf('75', plain,
% 0.85/1.04      (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.85/1.04      inference('simpl_trail', [status(thm)], ['1', '74'])).
% 0.85/1.04  thf('76', plain,
% 0.85/1.04      (![X21 : $i, X22 : $i]:
% 0.85/1.04         ((k2_xboole_0 @ X21 @ X22)
% 0.85/1.04           = (k5_xboole_0 @ X21 @ 
% 0.85/1.04              (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X22))))),
% 0.85/1.04      inference('demod', [status(thm)], ['56', '57'])).
% 0.85/1.04  thf('77', plain,
% 0.85/1.04      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.85/1.04         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.85/1.04           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.85/1.04      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.85/1.04  thf('78', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.85/1.04      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.04  thf('79', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.85/1.04           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.04      inference('sup+', [status(thm)], ['77', '78'])).
% 0.85/1.04  thf('80', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k2_xboole_0 @ X1 @ X0)
% 0.85/1.04           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.85/1.04      inference('sup+', [status(thm)], ['76', '79'])).
% 0.85/1.04  thf('81', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.85/1.04      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.04  thf('82', plain,
% 0.85/1.04      (![X6 : $i, X7 : $i]:
% 0.85/1.04         ((k4_xboole_0 @ X6 @ X7)
% 0.85/1.04           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.85/1.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.04  thf('83', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k2_xboole_0 @ X1 @ X0)
% 0.85/1.04           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.85/1.04      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.85/1.04  thf('84', plain,
% 0.85/1.04      (((k2_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C))
% 0.85/1.04         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 0.85/1.04      inference('sup+', [status(thm)], ['75', '83'])).
% 0.85/1.04  thf('85', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.85/1.04      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.04  thf('86', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.85/1.04      inference('sup+', [status(thm)], ['51', '52'])).
% 0.85/1.04  thf('87', plain,
% 0.85/1.04      (((k2_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C))
% 0.85/1.04         = (k2_tarski @ sk_B @ sk_C))),
% 0.85/1.04      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.85/1.04  thf(t7_xboole_1, axiom,
% 0.85/1.04    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.85/1.04  thf('88', plain,
% 0.85/1.04      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.85/1.04      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.85/1.04  thf('89', plain, ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))),
% 0.85/1.04      inference('sup+', [status(thm)], ['87', '88'])).
% 0.85/1.04  thf('90', plain,
% 0.85/1.04      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.85/1.04         (((X30) = (k2_tarski @ X28 @ X29))
% 0.85/1.04          | ((X30) = (k1_tarski @ X29))
% 0.85/1.04          | ((X30) = (k1_tarski @ X28))
% 0.85/1.04          | ((X30) = (k1_xboole_0))
% 0.85/1.04          | ~ (r1_tarski @ X30 @ (k2_tarski @ X28 @ X29)))),
% 0.85/1.04      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.85/1.04  thf('91', plain,
% 0.85/1.04      ((((sk_A) = (k1_xboole_0))
% 0.85/1.04        | ((sk_A) = (k1_tarski @ sk_B))
% 0.85/1.04        | ((sk_A) = (k1_tarski @ sk_C))
% 0.85/1.04        | ((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['89', '90'])).
% 0.85/1.04  thf('92', plain, (((sk_A) != (k2_tarski @ sk_B @ sk_C))),
% 0.85/1.04      inference('simpl_trail', [status(thm)], ['6', '18'])).
% 0.85/1.04  thf('93', plain,
% 0.85/1.04      ((((sk_A) != (k1_tarski @ sk_C))
% 0.85/1.04        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('94', plain,
% 0.85/1.04      ((((sk_A) != (k1_tarski @ sk_C))) <= (~ (((sk_A) = (k1_tarski @ sk_C))))),
% 0.85/1.04      inference('split', [status(esa)], ['93'])).
% 0.85/1.04  thf('95', plain,
% 0.85/1.04      (~ (((sk_A) = (k1_tarski @ sk_C))) | 
% 0.85/1.04       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.85/1.04      inference('split', [status(esa)], ['93'])).
% 0.85/1.04  thf('96', plain, (~ (((sk_A) = (k1_tarski @ sk_C)))),
% 0.85/1.04      inference('sat_resolution*', [status(thm)], ['73', '95'])).
% 0.85/1.04  thf('97', plain, (((sk_A) != (k1_tarski @ sk_C))),
% 0.85/1.04      inference('simpl_trail', [status(thm)], ['94', '96'])).
% 0.85/1.04  thf('98', plain,
% 0.85/1.04      ((((sk_A) != (k1_tarski @ sk_B))
% 0.85/1.04        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('99', plain,
% 0.85/1.04      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.85/1.04      inference('split', [status(esa)], ['98'])).
% 0.85/1.04  thf('100', plain,
% 0.85/1.04      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.85/1.04       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.85/1.04      inference('split', [status(esa)], ['98'])).
% 0.85/1.04  thf('101', plain, (~ (((sk_A) = (k1_tarski @ sk_B)))),
% 0.85/1.04      inference('sat_resolution*', [status(thm)], ['73', '100'])).
% 0.85/1.04  thf('102', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.85/1.04      inference('simpl_trail', [status(thm)], ['99', '101'])).
% 0.85/1.04  thf('103', plain,
% 0.85/1.04      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.85/1.04      inference('split', [status(esa)], ['2'])).
% 0.85/1.04  thf('104', plain,
% 0.85/1.04      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.85/1.04       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.85/1.04      inference('split', [status(esa)], ['2'])).
% 0.85/1.04  thf('105', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.85/1.04      inference('sat_resolution*', [status(thm)], ['73', '104'])).
% 0.85/1.04  thf('106', plain, (((sk_A) != (k1_xboole_0))),
% 0.85/1.04      inference('simpl_trail', [status(thm)], ['103', '105'])).
% 0.85/1.04  thf('107', plain, ($false),
% 0.85/1.04      inference('simplify_reflect-', [status(thm)],
% 0.85/1.04                ['91', '92', '97', '102', '106'])).
% 0.85/1.04  
% 0.85/1.04  % SZS output end Refutation
% 0.85/1.04  
% 0.85/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

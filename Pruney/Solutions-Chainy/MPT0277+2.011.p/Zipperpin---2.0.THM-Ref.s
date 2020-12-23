%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pN018IEVou

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:41 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  182 (1173 expanded)
%              Number of leaves         :   28 ( 373 expanded)
%              Depth                    :   26
%              Number of atoms          : 1542 (11253 expanded)
%              Number of equality atoms :  226 (1757 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
      = ( k2_tarski @ sk_B @ sk_C_2 ) )
    | ( sk_A
      = ( k1_tarski @ sk_C_2 ) )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C_2 ) )
    | ( sk_A
      = ( k1_tarski @ sk_C_2 ) )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C_2 ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C_2 ) )
   <= ( sk_A
     != ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C_2 ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('9',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C_2 ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
     != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
      = k1_xboole_0 )
    | ( sk_A
     != ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    sk_A
 != ( k2_tarski @ sk_B @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['7','17'])).

thf('19',plain,(
    sk_A
 != ( k2_tarski @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['6','18'])).

thf('20',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_C_2 ) )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','19'])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('22',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C_2 ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( sk_A
        = ( k1_tarski @ sk_C_2 ) )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
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
    ! [X40: $i,X42: $i,X43: $i] :
      ( ( r1_tarski @ X42 @ ( k2_tarski @ X40 @ X43 ) )
      | ( X42
       != ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('25',plain,(
    ! [X40: $i,X43: $i] :
      ( r1_tarski @ ( k1_tarski @ X43 ) @ ( k2_tarski @ X40 @ X43 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('33',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('39',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ X0 @ sk_C_2 ) )
          = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ( sk_A
          = ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','40'])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('43',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X40: $i,X42: $i,X43: $i] :
      ( ( r1_tarski @ X42 @ ( k2_tarski @ X40 @ X43 ) )
      | ( X42
       != ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('46',plain,(
    ! [X40: $i,X43: $i] :
      ( r1_tarski @ ( k1_tarski @ X40 ) @ ( k2_tarski @ X40 @ X43 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('52',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('53',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('58',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ X0 ) )
          = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','59'])).

thf('61',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('62',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('64',plain,(
    ! [X15: $i] :
      ( ( r1_xboole_0 @ X15 @ X15 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('65',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('66',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('67',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('68',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('80',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('88',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','63','89'])).

thf('91',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['91'])).

thf('93',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','92'])).

thf('94',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('96',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('99',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('107',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('108',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['103','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['97','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['94','111'])).

thf('113',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('116',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['97','110'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['114','123'])).

thf('125',plain,
    ( ( k5_xboole_0 @ ( k2_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) ) @ k1_xboole_0 )
    = ( k2_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['93','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['97','110'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
    = ( k2_tarski @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['125','128','131'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('133',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('134',plain,(
    r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X42
        = ( k2_tarski @ X40 @ X41 ) )
      | ( X42
        = ( k1_tarski @ X41 ) )
      | ( X42
        = ( k1_tarski @ X40 ) )
      | ( X42 = k1_xboole_0 )
      | ~ ( r1_tarski @ X42 @ ( k2_tarski @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('136',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A
      = ( k1_tarski @ sk_C_2 ) )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    sk_A
 != ( k2_tarski @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['6','18'])).

thf('138',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C_2 ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C_2 ) )
   <= ( sk_A
     != ( k1_tarski @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['138'])).

thf('140',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C_2 ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['138'])).

thf('141',plain,(
    sk_A
 != ( k1_tarski @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['91','140'])).

thf('142',plain,(
    sk_A
 != ( k1_tarski @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['139','141'])).

thf('143',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['143'])).

thf('145',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['143'])).

thf('146',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['91','145'])).

thf('147',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['144','146'])).

thf('148',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('149',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('150',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['91','149'])).

thf('151',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['148','150'])).

thf('152',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['136','137','142','147','151'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pN018IEVou
% 0.07/0.26  % Computer   : n001.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 17:30:15 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.26  % Running portfolio for 600 s
% 0.07/0.26  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.07/0.26  % Number of cores: 8
% 0.07/0.26  % Python version: Python 3.6.8
% 0.07/0.27  % Running in FO mode
% 0.51/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.71  % Solved by: fo/fo7.sh
% 0.51/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.71  % done 1160 iterations in 0.338s
% 0.51/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.71  % SZS output start Refutation
% 0.51/0.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.51/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.51/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.51/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.51/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.71  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.51/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.51/0.71  thf(t75_zfmisc_1, conjecture,
% 0.51/0.71    (![A:$i,B:$i,C:$i]:
% 0.51/0.71     ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.51/0.71       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.51/0.71            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.51/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.51/0.71        ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.51/0.71          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.51/0.71               ( ( A ) != ( k1_tarski @ C ) ) & 
% 0.51/0.71               ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ) )),
% 0.51/0.71    inference('cnf.neg', [status(esa)], [t75_zfmisc_1])).
% 0.51/0.71  thf('0', plain,
% 0.51/0.71      ((((sk_A) = (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71        | ((sk_A) = (k1_tarski @ sk_C_2))
% 0.51/0.71        | ((sk_A) = (k1_tarski @ sk_B))
% 0.51/0.71        | ((sk_A) = (k1_xboole_0))
% 0.51/0.71        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) = (k1_xboole_0)))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('1', plain,
% 0.51/0.71      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) = (k1_xboole_0)))
% 0.51/0.71         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71                = (k1_xboole_0))))),
% 0.51/0.71      inference('split', [status(esa)], ['0'])).
% 0.51/0.71  thf('2', plain,
% 0.51/0.71      ((((sk_A) != (k1_xboole_0))
% 0.51/0.71        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) != (k1_xboole_0)))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('3', plain,
% 0.51/0.71      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) != (k1_xboole_0)))
% 0.51/0.71         <= (~
% 0.51/0.71             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71                = (k1_xboole_0))))),
% 0.51/0.71      inference('split', [status(esa)], ['2'])).
% 0.51/0.71  thf('4', plain,
% 0.51/0.71      ((((sk_A) = (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71        | ((sk_A) = (k1_tarski @ sk_C_2))
% 0.51/0.71        | ((sk_A) = (k1_tarski @ sk_B))
% 0.51/0.71        | ((sk_A) = (k1_xboole_0))
% 0.51/0.71        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) = (k1_xboole_0)))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('5', plain,
% 0.51/0.71      ((((sk_A) != (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) != (k1_xboole_0)))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('6', plain,
% 0.51/0.71      ((((sk_A) != (k2_tarski @ sk_B @ sk_C_2)))
% 0.51/0.71         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C_2))))),
% 0.51/0.71      inference('split', [status(esa)], ['5'])).
% 0.51/0.71  thf('7', plain,
% 0.51/0.71      (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C_2))) | 
% 0.51/0.71       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) = (k1_xboole_0)))),
% 0.51/0.71      inference('split', [status(esa)], ['5'])).
% 0.51/0.71  thf(t92_xboole_1, axiom,
% 0.51/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.51/0.71  thf('8', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.51/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.51/0.71  thf(idempotence_k3_xboole_0, axiom,
% 0.51/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.51/0.71  thf('9', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.51/0.71      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.51/0.71  thf(t100_xboole_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.51/0.71  thf('10', plain,
% 0.51/0.71      (![X10 : $i, X11 : $i]:
% 0.51/0.71         ((k4_xboole_0 @ X10 @ X11)
% 0.51/0.71           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.51/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.71  thf('11', plain,
% 0.51/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf('12', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.51/0.71      inference('demod', [status(thm)], ['8', '11'])).
% 0.51/0.71  thf('13', plain,
% 0.51/0.71      ((((sk_A) = (k2_tarski @ sk_B @ sk_C_2)))
% 0.51/0.71         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C_2))))),
% 0.51/0.71      inference('split', [status(esa)], ['0'])).
% 0.51/0.71  thf('14', plain,
% 0.51/0.71      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) != (k1_xboole_0)))
% 0.51/0.71         <= (~
% 0.51/0.71             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71                = (k1_xboole_0))))),
% 0.51/0.71      inference('split', [status(esa)], ['2'])).
% 0.51/0.71  thf('15', plain,
% 0.51/0.71      ((((k4_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0)))
% 0.51/0.71         <= (~
% 0.51/0.71             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71                = (k1_xboole_0))) & 
% 0.51/0.71             (((sk_A) = (k2_tarski @ sk_B @ sk_C_2))))),
% 0.51/0.71      inference('sup-', [status(thm)], ['13', '14'])).
% 0.51/0.71  thf('16', plain,
% 0.51/0.71      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.51/0.71         <= (~
% 0.51/0.71             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71                = (k1_xboole_0))) & 
% 0.51/0.71             (((sk_A) = (k2_tarski @ sk_B @ sk_C_2))))),
% 0.51/0.71      inference('sup-', [status(thm)], ['12', '15'])).
% 0.51/0.71  thf('17', plain,
% 0.51/0.71      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) = (k1_xboole_0))) | 
% 0.51/0.71       ~ (((sk_A) = (k2_tarski @ sk_B @ sk_C_2)))),
% 0.51/0.71      inference('simplify', [status(thm)], ['16'])).
% 0.51/0.71  thf('18', plain, (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C_2)))),
% 0.51/0.71      inference('sat_resolution*', [status(thm)], ['7', '17'])).
% 0.51/0.71  thf('19', plain, (((sk_A) != (k2_tarski @ sk_B @ sk_C_2))),
% 0.51/0.71      inference('simpl_trail', [status(thm)], ['6', '18'])).
% 0.51/0.71  thf('20', plain,
% 0.51/0.71      ((((sk_A) = (k1_tarski @ sk_C_2))
% 0.51/0.71        | ((sk_A) = (k1_tarski @ sk_B))
% 0.51/0.71        | ((sk_A) = (k1_xboole_0))
% 0.51/0.71        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) = (k1_xboole_0)))),
% 0.51/0.71      inference('simplify_reflect-', [status(thm)], ['4', '19'])).
% 0.51/0.71  thf('21', plain,
% 0.51/0.71      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) != (k1_xboole_0)))
% 0.51/0.71         <= (~
% 0.51/0.71             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71                = (k1_xboole_0))))),
% 0.51/0.71      inference('split', [status(esa)], ['2'])).
% 0.51/0.71  thf('22', plain,
% 0.51/0.71      (((((k1_xboole_0) != (k1_xboole_0))
% 0.51/0.71         | ((sk_A) = (k1_xboole_0))
% 0.51/0.71         | ((sk_A) = (k1_tarski @ sk_B))
% 0.51/0.71         | ((sk_A) = (k1_tarski @ sk_C_2))))
% 0.51/0.71         <= (~
% 0.51/0.71             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71                = (k1_xboole_0))))),
% 0.51/0.71      inference('sup-', [status(thm)], ['20', '21'])).
% 0.51/0.71  thf('23', plain,
% 0.51/0.71      (((((sk_A) = (k1_tarski @ sk_C_2))
% 0.51/0.71         | ((sk_A) = (k1_tarski @ sk_B))
% 0.51/0.71         | ((sk_A) = (k1_xboole_0))))
% 0.51/0.71         <= (~
% 0.51/0.71             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71                = (k1_xboole_0))))),
% 0.51/0.71      inference('simplify', [status(thm)], ['22'])).
% 0.51/0.71  thf(l45_zfmisc_1, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i]:
% 0.51/0.71     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.51/0.71       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.51/0.71            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.51/0.71  thf('24', plain,
% 0.51/0.71      (![X40 : $i, X42 : $i, X43 : $i]:
% 0.51/0.71         ((r1_tarski @ X42 @ (k2_tarski @ X40 @ X43))
% 0.51/0.71          | ((X42) != (k1_tarski @ X43)))),
% 0.51/0.71      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.51/0.71  thf('25', plain,
% 0.51/0.71      (![X40 : $i, X43 : $i]:
% 0.51/0.71         (r1_tarski @ (k1_tarski @ X43) @ (k2_tarski @ X40 @ X43))),
% 0.51/0.71      inference('simplify', [status(thm)], ['24'])).
% 0.51/0.71  thf(t12_xboole_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.51/0.71  thf('26', plain,
% 0.51/0.71      (![X12 : $i, X13 : $i]:
% 0.51/0.71         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.51/0.71      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.51/0.71  thf('27', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.51/0.71           = (k2_tarski @ X1 @ X0))),
% 0.51/0.71      inference('sup-', [status(thm)], ['25', '26'])).
% 0.51/0.71  thf(t95_xboole_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( k3_xboole_0 @ A @ B ) =
% 0.51/0.71       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.51/0.71  thf('28', plain,
% 0.51/0.71      (![X23 : $i, X24 : $i]:
% 0.51/0.71         ((k3_xboole_0 @ X23 @ X24)
% 0.51/0.71           = (k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ 
% 0.51/0.71              (k2_xboole_0 @ X23 @ X24)))),
% 0.51/0.71      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.51/0.71  thf(t91_xboole_1, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i]:
% 0.51/0.71     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.51/0.71       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.51/0.71  thf('29', plain,
% 0.51/0.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.51/0.71           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.51/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.51/0.71  thf('30', plain,
% 0.51/0.71      (![X23 : $i, X24 : $i]:
% 0.51/0.71         ((k3_xboole_0 @ X23 @ X24)
% 0.51/0.71           = (k5_xboole_0 @ X23 @ 
% 0.51/0.71              (k5_xboole_0 @ X24 @ (k2_xboole_0 @ X23 @ X24))))),
% 0.51/0.71      inference('demod', [status(thm)], ['28', '29'])).
% 0.51/0.71  thf('31', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.51/0.71           = (k5_xboole_0 @ (k1_tarski @ X0) @ 
% 0.51/0.71              (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X1 @ X0))))),
% 0.51/0.71      inference('sup+', [status(thm)], ['27', '30'])).
% 0.51/0.71  thf('32', plain,
% 0.51/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf('33', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.51/0.71      inference('demod', [status(thm)], ['8', '11'])).
% 0.51/0.71  thf(t5_boole, axiom,
% 0.51/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.51/0.71  thf('34', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.51/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.51/0.71  thf('35', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.51/0.71           = (k1_tarski @ X0))),
% 0.51/0.71      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.51/0.71  thf('36', plain,
% 0.51/0.71      (![X10 : $i, X11 : $i]:
% 0.51/0.71         ((k4_xboole_0 @ X10 @ X11)
% 0.51/0.71           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.51/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.71  thf('37', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.51/0.71           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.51/0.71      inference('sup+', [status(thm)], ['35', '36'])).
% 0.51/0.71  thf('38', plain,
% 0.51/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf('39', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.51/0.71      inference('demod', [status(thm)], ['8', '11'])).
% 0.51/0.71  thf('40', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.51/0.71           = (k1_xboole_0))),
% 0.51/0.71      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.51/0.71  thf('41', plain,
% 0.51/0.71      ((![X0 : $i]:
% 0.51/0.71          (((k4_xboole_0 @ sk_A @ (k2_tarski @ X0 @ sk_C_2)) = (k1_xboole_0))
% 0.51/0.71           | ((sk_A) = (k1_xboole_0))
% 0.51/0.71           | ((sk_A) = (k1_tarski @ sk_B))))
% 0.51/0.71         <= (~
% 0.51/0.71             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71                = (k1_xboole_0))))),
% 0.51/0.71      inference('sup+', [status(thm)], ['23', '40'])).
% 0.51/0.71  thf('42', plain,
% 0.51/0.71      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) != (k1_xboole_0)))
% 0.51/0.71         <= (~
% 0.51/0.71             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71                = (k1_xboole_0))))),
% 0.51/0.71      inference('split', [status(esa)], ['2'])).
% 0.51/0.71  thf('43', plain,
% 0.51/0.71      (((((k1_xboole_0) != (k1_xboole_0))
% 0.51/0.71         | ((sk_A) = (k1_tarski @ sk_B))
% 0.51/0.71         | ((sk_A) = (k1_xboole_0))))
% 0.51/0.71         <= (~
% 0.51/0.71             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71                = (k1_xboole_0))))),
% 0.51/0.71      inference('sup-', [status(thm)], ['41', '42'])).
% 0.51/0.71  thf('44', plain,
% 0.51/0.71      (((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B))))
% 0.51/0.71         <= (~
% 0.51/0.71             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71                = (k1_xboole_0))))),
% 0.51/0.71      inference('simplify', [status(thm)], ['43'])).
% 0.51/0.71  thf('45', plain,
% 0.51/0.71      (![X40 : $i, X42 : $i, X43 : $i]:
% 0.51/0.71         ((r1_tarski @ X42 @ (k2_tarski @ X40 @ X43))
% 0.51/0.71          | ((X42) != (k1_tarski @ X40)))),
% 0.51/0.71      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.51/0.71  thf('46', plain,
% 0.51/0.71      (![X40 : $i, X43 : $i]:
% 0.51/0.71         (r1_tarski @ (k1_tarski @ X40) @ (k2_tarski @ X40 @ X43))),
% 0.51/0.71      inference('simplify', [status(thm)], ['45'])).
% 0.51/0.71  thf('47', plain,
% 0.51/0.71      (![X12 : $i, X13 : $i]:
% 0.51/0.71         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.51/0.71      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.51/0.71  thf('48', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.51/0.71           = (k2_tarski @ X1 @ X0))),
% 0.51/0.71      inference('sup-', [status(thm)], ['46', '47'])).
% 0.51/0.71  thf('49', plain,
% 0.51/0.71      (![X23 : $i, X24 : $i]:
% 0.51/0.71         ((k3_xboole_0 @ X23 @ X24)
% 0.51/0.71           = (k5_xboole_0 @ X23 @ 
% 0.51/0.71              (k5_xboole_0 @ X24 @ (k2_xboole_0 @ X23 @ X24))))),
% 0.51/0.71      inference('demod', [status(thm)], ['28', '29'])).
% 0.51/0.71  thf('50', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.51/0.71           = (k5_xboole_0 @ (k1_tarski @ X1) @ 
% 0.51/0.71              (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X1 @ X0))))),
% 0.51/0.71      inference('sup+', [status(thm)], ['48', '49'])).
% 0.51/0.71  thf('51', plain,
% 0.51/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf('52', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.51/0.71      inference('demod', [status(thm)], ['8', '11'])).
% 0.51/0.71  thf('53', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.51/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.51/0.71  thf('54', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.51/0.71           = (k1_tarski @ X1))),
% 0.51/0.71      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.51/0.71  thf('55', plain,
% 0.51/0.71      (![X10 : $i, X11 : $i]:
% 0.51/0.71         ((k4_xboole_0 @ X10 @ X11)
% 0.51/0.71           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.51/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.71  thf('56', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.51/0.71           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.51/0.71      inference('sup+', [status(thm)], ['54', '55'])).
% 0.51/0.71  thf('57', plain,
% 0.51/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf('58', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.51/0.71      inference('demod', [status(thm)], ['8', '11'])).
% 0.51/0.71  thf('59', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.51/0.71           = (k1_xboole_0))),
% 0.51/0.71      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.51/0.71  thf('60', plain,
% 0.51/0.71      ((![X0 : $i]:
% 0.51/0.71          (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ X0)) = (k1_xboole_0))
% 0.51/0.71           | ((sk_A) = (k1_xboole_0))))
% 0.51/0.71         <= (~
% 0.51/0.71             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71                = (k1_xboole_0))))),
% 0.51/0.71      inference('sup+', [status(thm)], ['44', '59'])).
% 0.51/0.71  thf('61', plain,
% 0.51/0.71      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) != (k1_xboole_0)))
% 0.51/0.71         <= (~
% 0.51/0.71             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71                = (k1_xboole_0))))),
% 0.51/0.71      inference('split', [status(esa)], ['2'])).
% 0.51/0.71  thf('62', plain,
% 0.51/0.71      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.51/0.71         <= (~
% 0.51/0.71             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71                = (k1_xboole_0))))),
% 0.51/0.71      inference('sup-', [status(thm)], ['60', '61'])).
% 0.51/0.71  thf('63', plain,
% 0.51/0.71      ((((sk_A) = (k1_xboole_0)))
% 0.51/0.71         <= (~
% 0.51/0.71             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71                = (k1_xboole_0))))),
% 0.51/0.71      inference('simplify', [status(thm)], ['62'])).
% 0.51/0.71  thf(t66_xboole_1, axiom,
% 0.51/0.71    (![A:$i]:
% 0.51/0.71     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.51/0.71       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.51/0.71  thf('64', plain,
% 0.51/0.71      (![X15 : $i]: ((r1_xboole_0 @ X15 @ X15) | ((X15) != (k1_xboole_0)))),
% 0.51/0.71      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.51/0.71  thf('65', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.51/0.71      inference('simplify', [status(thm)], ['64'])).
% 0.51/0.71  thf(d3_tarski, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( r1_tarski @ A @ B ) <=>
% 0.51/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.51/0.71  thf('66', plain,
% 0.51/0.71      (![X1 : $i, X3 : $i]:
% 0.51/0.71         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.51/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.71  thf('67', plain,
% 0.51/0.71      (![X1 : $i, X3 : $i]:
% 0.51/0.71         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.51/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.71  thf(t3_xboole_0, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.51/0.71            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.51/0.71       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.51/0.71            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.51/0.71  thf('68', plain,
% 0.51/0.71      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X8 @ X6)
% 0.51/0.71          | ~ (r2_hidden @ X8 @ X9)
% 0.51/0.71          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.51/0.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.51/0.71  thf('69', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.71         ((r1_tarski @ X0 @ X1)
% 0.51/0.71          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.51/0.71          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.51/0.71      inference('sup-', [status(thm)], ['67', '68'])).
% 0.51/0.71  thf('70', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((r1_tarski @ X0 @ X1)
% 0.51/0.71          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.51/0.71          | (r1_tarski @ X0 @ X1))),
% 0.51/0.71      inference('sup-', [status(thm)], ['66', '69'])).
% 0.51/0.71  thf('71', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (r1_tarski @ X0 @ X1))),
% 0.51/0.71      inference('simplify', [status(thm)], ['70'])).
% 0.51/0.71  thf('72', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.51/0.71      inference('sup-', [status(thm)], ['65', '71'])).
% 0.51/0.71  thf('73', plain,
% 0.51/0.71      (![X12 : $i, X13 : $i]:
% 0.51/0.71         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.51/0.71      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.51/0.71  thf('74', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.71      inference('sup-', [status(thm)], ['72', '73'])).
% 0.51/0.71  thf('75', plain,
% 0.51/0.71      (![X23 : $i, X24 : $i]:
% 0.51/0.71         ((k3_xboole_0 @ X23 @ X24)
% 0.51/0.71           = (k5_xboole_0 @ X23 @ 
% 0.51/0.71              (k5_xboole_0 @ X24 @ (k2_xboole_0 @ X23 @ X24))))),
% 0.51/0.71      inference('demod', [status(thm)], ['28', '29'])).
% 0.51/0.71  thf('76', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.51/0.71           = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.51/0.71      inference('sup+', [status(thm)], ['74', '75'])).
% 0.51/0.71  thf('77', plain,
% 0.51/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf('78', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.51/0.71           = (k5_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.51/0.71      inference('demod', [status(thm)], ['76', '77'])).
% 0.51/0.71  thf('79', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.51/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.51/0.71  thf('80', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.51/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.51/0.71  thf('81', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 0.51/0.71      inference('sup+', [status(thm)], ['79', '80'])).
% 0.51/0.71  thf('82', plain,
% 0.51/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf('83', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.51/0.71      inference('demod', [status(thm)], ['81', '82'])).
% 0.51/0.71  thf('84', plain,
% 0.51/0.71      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.51/0.71      inference('demod', [status(thm)], ['78', '83'])).
% 0.51/0.71  thf('85', plain,
% 0.51/0.71      (![X10 : $i, X11 : $i]:
% 0.51/0.71         ((k4_xboole_0 @ X10 @ X11)
% 0.51/0.71           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.51/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.71  thf('86', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.51/0.71           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['84', '85'])).
% 0.51/0.71  thf('87', plain,
% 0.51/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf('88', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.51/0.71      inference('demod', [status(thm)], ['8', '11'])).
% 0.51/0.71  thf('89', plain,
% 0.51/0.71      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.51/0.71      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.51/0.71  thf('90', plain,
% 0.51/0.71      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.51/0.71         <= (~
% 0.51/0.71             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71                = (k1_xboole_0))))),
% 0.51/0.71      inference('demod', [status(thm)], ['3', '63', '89'])).
% 0.51/0.71  thf('91', plain,
% 0.51/0.71      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) = (k1_xboole_0)))),
% 0.51/0.71      inference('simplify', [status(thm)], ['90'])).
% 0.51/0.71  thf('92', plain,
% 0.51/0.71      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) = (k1_xboole_0)))),
% 0.51/0.71      inference('sat_resolution*', [status(thm)], ['91'])).
% 0.51/0.71  thf('93', plain,
% 0.51/0.71      (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) = (k1_xboole_0))),
% 0.51/0.71      inference('simpl_trail', [status(thm)], ['1', '92'])).
% 0.51/0.71  thf('94', plain,
% 0.51/0.71      (![X23 : $i, X24 : $i]:
% 0.51/0.71         ((k3_xboole_0 @ X23 @ X24)
% 0.51/0.71           = (k5_xboole_0 @ X23 @ 
% 0.51/0.71              (k5_xboole_0 @ X24 @ (k2_xboole_0 @ X23 @ X24))))),
% 0.51/0.71      inference('demod', [status(thm)], ['28', '29'])).
% 0.51/0.71  thf('95', plain,
% 0.51/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf('96', plain,
% 0.51/0.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.51/0.71           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.51/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.51/0.71  thf('97', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.51/0.71           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.51/0.71      inference('sup+', [status(thm)], ['95', '96'])).
% 0.51/0.71  thf('98', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.51/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.51/0.71  thf('99', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.51/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.51/0.71  thf('100', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X1) = (k5_xboole_0 @ X0 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['98', '99'])).
% 0.51/0.71  thf('101', plain,
% 0.51/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf('102', plain,
% 0.51/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf('103', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X1 @ X1) = (k4_xboole_0 @ X0 @ X0))),
% 0.51/0.71      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.51/0.71  thf('104', plain,
% 0.51/0.71      (![X23 : $i, X24 : $i]:
% 0.51/0.71         ((k3_xboole_0 @ X23 @ X24)
% 0.51/0.71           = (k5_xboole_0 @ X23 @ 
% 0.51/0.71              (k5_xboole_0 @ X24 @ (k2_xboole_0 @ X23 @ X24))))),
% 0.51/0.71      inference('demod', [status(thm)], ['28', '29'])).
% 0.51/0.71  thf('105', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.51/0.71           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.51/0.71      inference('sup+', [status(thm)], ['95', '96'])).
% 0.51/0.71  thf('106', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k2_xboole_0 @ X0 @ X0))
% 0.51/0.71           = (k3_xboole_0 @ X0 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['104', '105'])).
% 0.51/0.71  thf(idempotence_k2_xboole_0, axiom,
% 0.51/0.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.51/0.71  thf('107', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.51/0.71      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.51/0.71  thf('108', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.51/0.71      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.51/0.71  thf('109', plain,
% 0.51/0.71      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.51/0.71      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.51/0.71  thf('110', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.51/0.71      inference('sup+', [status(thm)], ['103', '109'])).
% 0.51/0.71  thf('111', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.51/0.71      inference('demod', [status(thm)], ['97', '110'])).
% 0.51/0.71  thf('112', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.51/0.71           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.51/0.71      inference('sup+', [status(thm)], ['94', '111'])).
% 0.51/0.71  thf('113', plain,
% 0.51/0.71      (![X10 : $i, X11 : $i]:
% 0.51/0.71         ((k4_xboole_0 @ X10 @ X11)
% 0.51/0.71           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.51/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.71  thf('114', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.51/0.71           = (k4_xboole_0 @ X1 @ X0))),
% 0.51/0.71      inference('demod', [status(thm)], ['112', '113'])).
% 0.51/0.71  thf('115', plain,
% 0.51/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf('116', plain,
% 0.51/0.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.51/0.71           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.51/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.51/0.71  thf('117', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.51/0.71           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.51/0.71      inference('sup+', [status(thm)], ['115', '116'])).
% 0.51/0.71  thf('118', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.51/0.71      inference('demod', [status(thm)], ['8', '11'])).
% 0.51/0.71  thf('119', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k1_xboole_0)
% 0.51/0.71           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.51/0.71      inference('demod', [status(thm)], ['117', '118'])).
% 0.51/0.71  thf('120', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.51/0.71      inference('demod', [status(thm)], ['97', '110'])).
% 0.51/0.71  thf('121', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.51/0.71           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['119', '120'])).
% 0.51/0.71  thf('122', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.51/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.51/0.71  thf('123', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.51/0.71      inference('demod', [status(thm)], ['121', '122'])).
% 0.51/0.71  thf('124', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.51/0.71           = (X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['114', '123'])).
% 0.51/0.71  thf('125', plain,
% 0.51/0.71      (((k5_xboole_0 @ (k2_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) @ 
% 0.51/0.71         k1_xboole_0) = (k2_tarski @ sk_B @ sk_C_2))),
% 0.51/0.71      inference('sup+', [status(thm)], ['93', '124'])).
% 0.51/0.71  thf('126', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.51/0.71      inference('demod', [status(thm)], ['121', '122'])).
% 0.51/0.71  thf('127', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.51/0.71      inference('demod', [status(thm)], ['97', '110'])).
% 0.51/0.71  thf('128', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['126', '127'])).
% 0.51/0.71  thf('129', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.51/0.71      inference('demod', [status(thm)], ['8', '11'])).
% 0.51/0.71  thf('130', plain,
% 0.51/0.71      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.51/0.71      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.51/0.71  thf('131', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['129', '130'])).
% 0.51/0.71  thf('132', plain,
% 0.51/0.71      (((k2_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))
% 0.51/0.71         = (k2_tarski @ sk_B @ sk_C_2))),
% 0.51/0.71      inference('demod', [status(thm)], ['125', '128', '131'])).
% 0.51/0.71  thf(t7_xboole_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.51/0.71  thf('133', plain,
% 0.51/0.71      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.51/0.71      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.51/0.71  thf('134', plain, ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))),
% 0.51/0.71      inference('sup+', [status(thm)], ['132', '133'])).
% 0.51/0.71  thf('135', plain,
% 0.51/0.71      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.51/0.71         (((X42) = (k2_tarski @ X40 @ X41))
% 0.51/0.71          | ((X42) = (k1_tarski @ X41))
% 0.51/0.71          | ((X42) = (k1_tarski @ X40))
% 0.51/0.71          | ((X42) = (k1_xboole_0))
% 0.51/0.71          | ~ (r1_tarski @ X42 @ (k2_tarski @ X40 @ X41)))),
% 0.51/0.71      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.51/0.71  thf('136', plain,
% 0.51/0.71      ((((sk_A) = (k1_xboole_0))
% 0.51/0.71        | ((sk_A) = (k1_tarski @ sk_B))
% 0.51/0.71        | ((sk_A) = (k1_tarski @ sk_C_2))
% 0.51/0.71        | ((sk_A) = (k2_tarski @ sk_B @ sk_C_2)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['134', '135'])).
% 0.51/0.71  thf('137', plain, (((sk_A) != (k2_tarski @ sk_B @ sk_C_2))),
% 0.51/0.71      inference('simpl_trail', [status(thm)], ['6', '18'])).
% 0.51/0.71  thf('138', plain,
% 0.51/0.71      ((((sk_A) != (k1_tarski @ sk_C_2))
% 0.51/0.71        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) != (k1_xboole_0)))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('139', plain,
% 0.51/0.71      ((((sk_A) != (k1_tarski @ sk_C_2)))
% 0.51/0.71         <= (~ (((sk_A) = (k1_tarski @ sk_C_2))))),
% 0.51/0.71      inference('split', [status(esa)], ['138'])).
% 0.51/0.71  thf('140', plain,
% 0.51/0.71      (~ (((sk_A) = (k1_tarski @ sk_C_2))) | 
% 0.51/0.71       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) = (k1_xboole_0)))),
% 0.51/0.71      inference('split', [status(esa)], ['138'])).
% 0.51/0.71  thf('141', plain, (~ (((sk_A) = (k1_tarski @ sk_C_2)))),
% 0.51/0.71      inference('sat_resolution*', [status(thm)], ['91', '140'])).
% 0.51/0.71  thf('142', plain, (((sk_A) != (k1_tarski @ sk_C_2))),
% 0.51/0.71      inference('simpl_trail', [status(thm)], ['139', '141'])).
% 0.51/0.71  thf('143', plain,
% 0.51/0.71      ((((sk_A) != (k1_tarski @ sk_B))
% 0.51/0.71        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) != (k1_xboole_0)))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('144', plain,
% 0.51/0.71      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.51/0.71      inference('split', [status(esa)], ['143'])).
% 0.51/0.71  thf('145', plain,
% 0.51/0.71      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.51/0.71       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) = (k1_xboole_0)))),
% 0.51/0.71      inference('split', [status(esa)], ['143'])).
% 0.51/0.71  thf('146', plain, (~ (((sk_A) = (k1_tarski @ sk_B)))),
% 0.51/0.71      inference('sat_resolution*', [status(thm)], ['91', '145'])).
% 0.51/0.71  thf('147', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.51/0.71      inference('simpl_trail', [status(thm)], ['144', '146'])).
% 0.51/0.71  thf('148', plain,
% 0.51/0.71      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.51/0.71      inference('split', [status(esa)], ['2'])).
% 0.51/0.71  thf('149', plain,
% 0.51/0.71      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.51/0.71       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)) = (k1_xboole_0)))),
% 0.51/0.71      inference('split', [status(esa)], ['2'])).
% 0.51/0.71  thf('150', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.51/0.71      inference('sat_resolution*', [status(thm)], ['91', '149'])).
% 0.51/0.71  thf('151', plain, (((sk_A) != (k1_xboole_0))),
% 0.51/0.71      inference('simpl_trail', [status(thm)], ['148', '150'])).
% 0.51/0.71  thf('152', plain, ($false),
% 0.51/0.71      inference('simplify_reflect-', [status(thm)],
% 0.51/0.71                ['136', '137', '142', '147', '151'])).
% 0.51/0.71  
% 0.51/0.71  % SZS output end Refutation
% 0.51/0.71  
% 0.51/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CYyEpP800x

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:41 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  183 (2128 expanded)
%              Number of leaves         :   26 ( 638 expanded)
%              Depth                    :   29
%              Number of atoms          : 1628 (22244 expanded)
%              Number of equality atoms :  259 (3722 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
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
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ X13 )
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

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('24',plain,(
    ! [X43: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('25',plain,
    ( ( ( ( k3_tarski @ sk_A )
        = sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t42_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('26',plain,(
    ! [X44: $i,X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ ( k2_tarski @ X44 @ X47 ) )
      | ( X46
       != ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t42_zfmisc_1])).

thf('27',plain,(
    ! [X44: $i,X47: $i] :
      ( r1_tarski @ ( k1_tarski @ X44 ) @ ( k2_tarski @ X44 @ X47 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6
        = ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6
        = ( k2_xboole_0 @ X5 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6
        = ( k2_xboole_0 @ X5 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('40',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('42',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['31','47'])).

thf('49',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ X0 ) )
          = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ( ( k3_tarski @ sk_A )
          = sk_C ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','50'])).

thf('52',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('53',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k3_tarski @ sk_A )
        = sk_C )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k3_tarski @ sk_A )
        = sk_C ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('56',plain,(
    ! [X44: $i,X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ ( k2_tarski @ X44 @ X47 ) )
      | ( X46
       != ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t42_zfmisc_1])).

thf('57',plain,(
    ! [X44: $i,X47: $i] :
      ( r1_tarski @ ( k1_tarski @ X47 ) @ ( k2_tarski @ X44 @ X47 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6
        = ( k2_xboole_0 @ X5 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ X0 @ sk_C ) )
          = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ( sk_A
          = ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','63'])).

thf('65',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('66',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X43: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('69',plain,
    ( ( ( ( k3_tarski @ sk_A )
        = sk_B )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( sk_C = sk_B )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','69'])).

thf('71',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_C = sk_B ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    sk_A
 != ( k2_tarski @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['6','18'])).

thf('73',plain,
    ( ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('74',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('75',plain,
    ( ( ( sk_A
       != ( k1_tarski @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('77',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('79',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('81',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('85',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X41 @ X42 ) )
      = ( k2_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X43: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['83','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['78','90'])).

thf('92',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X44: $i,X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ ( k2_tarski @ X44 @ X47 ) )
      | ( X46 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t42_zfmisc_1])).

thf('95',plain,(
    ! [X44: $i,X47: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X44 @ X47 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6
        = ( k2_xboole_0 @ X5 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('101',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('103',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100','101','102','103'])).

thf('105',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','77','93','104'])).

thf('106',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['106'])).

thf('108',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','107'])).

thf('109',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('111',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('112',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['83','88','89'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['110','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','116'])).

thf('118',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['110','115'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['108','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('124',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['110','115'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['110','115'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['78','90'])).

thf('135',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['122','133','134'])).

thf('136',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('137',plain,(
    r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X46
        = ( k2_tarski @ X44 @ X45 ) )
      | ( X46
        = ( k1_tarski @ X45 ) )
      | ( X46
        = ( k1_tarski @ X44 ) )
      | ( X46 = k1_xboole_0 )
      | ~ ( r1_tarski @ X46 @ ( k2_tarski @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t42_zfmisc_1])).

thf('139',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    sk_A
 != ( k2_tarski @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['6','18'])).

thf('141',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
   <= ( sk_A
     != ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['141'])).

thf('143',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['141'])).

thf('144',plain,(
    sk_A
 != ( k1_tarski @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['106','143'])).

thf('145',plain,(
    sk_A
 != ( k1_tarski @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['142','144'])).

thf('146',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['146'])).

thf('148',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['146'])).

thf('149',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['106','148'])).

thf('150',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['147','149'])).

thf('151',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('152',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('153',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['106','152'])).

thf('154',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['151','153'])).

thf('155',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['139','140','145','150','154'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CYyEpP800x
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:31:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.69/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.89  % Solved by: fo/fo7.sh
% 0.69/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.89  % done 1275 iterations in 0.444s
% 0.69/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.89  % SZS output start Refutation
% 0.69/0.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.89  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.69/0.89  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.69/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.69/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.69/0.89  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.69/0.89  thf(t75_zfmisc_1, conjecture,
% 0.69/0.89    (![A:$i,B:$i,C:$i]:
% 0.69/0.89     ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.69/0.89       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.69/0.89            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.69/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.89    (~( ![A:$i,B:$i,C:$i]:
% 0.69/0.89        ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.69/0.89          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.69/0.89               ( ( A ) != ( k1_tarski @ C ) ) & 
% 0.69/0.89               ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ) )),
% 0.69/0.89    inference('cnf.neg', [status(esa)], [t75_zfmisc_1])).
% 0.69/0.89  thf('0', plain,
% 0.69/0.89      ((((sk_A) = (k2_tarski @ sk_B @ sk_C))
% 0.69/0.89        | ((sk_A) = (k1_tarski @ sk_C))
% 0.69/0.89        | ((sk_A) = (k1_tarski @ sk_B))
% 0.69/0.89        | ((sk_A) = (k1_xboole_0))
% 0.69/0.89        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('1', plain,
% 0.69/0.89      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))
% 0.69/0.89         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('split', [status(esa)], ['0'])).
% 0.69/0.89  thf('2', plain,
% 0.69/0.89      ((((sk_A) != (k1_xboole_0))
% 0.69/0.89        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('3', plain,
% 0.69/0.89      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('split', [status(esa)], ['2'])).
% 0.69/0.89  thf('4', plain,
% 0.69/0.89      ((((sk_A) = (k2_tarski @ sk_B @ sk_C))
% 0.69/0.89        | ((sk_A) = (k1_tarski @ sk_C))
% 0.69/0.89        | ((sk_A) = (k1_tarski @ sk_B))
% 0.69/0.89        | ((sk_A) = (k1_xboole_0))
% 0.69/0.89        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('5', plain,
% 0.69/0.89      ((((sk_A) != (k2_tarski @ sk_B @ sk_C))
% 0.69/0.89        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('6', plain,
% 0.69/0.89      ((((sk_A) != (k2_tarski @ sk_B @ sk_C)))
% 0.69/0.89         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.69/0.89      inference('split', [status(esa)], ['5'])).
% 0.69/0.89  thf('7', plain,
% 0.69/0.89      (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) | 
% 0.69/0.89       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.69/0.89      inference('split', [status(esa)], ['5'])).
% 0.69/0.89  thf(t92_xboole_1, axiom,
% 0.69/0.89    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.69/0.89  thf('8', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.69/0.89  thf(idempotence_k3_xboole_0, axiom,
% 0.69/0.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.69/0.89  thf('9', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.69/0.89      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.69/0.89  thf(t100_xboole_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.69/0.89  thf('10', plain,
% 0.69/0.89      (![X1 : $i, X2 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ X1 @ X2)
% 0.69/0.89           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.69/0.89  thf('11', plain,
% 0.69/0.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['9', '10'])).
% 0.69/0.89  thf('12', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.69/0.89      inference('demod', [status(thm)], ['8', '11'])).
% 0.69/0.89  thf('13', plain,
% 0.69/0.89      ((((sk_A) = (k2_tarski @ sk_B @ sk_C)))
% 0.69/0.89         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.69/0.89      inference('split', [status(esa)], ['0'])).
% 0.69/0.89  thf('14', plain,
% 0.69/0.89      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('split', [status(esa)], ['2'])).
% 0.69/0.89  thf('15', plain,
% 0.69/0.89      ((((k4_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0)))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.69/0.89             (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['13', '14'])).
% 0.69/0.89  thf('16', plain,
% 0.69/0.89      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.69/0.89             (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['12', '15'])).
% 0.69/0.89  thf('17', plain,
% 0.69/0.89      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.69/0.89       ~ (((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 0.69/0.89      inference('simplify', [status(thm)], ['16'])).
% 0.69/0.89  thf('18', plain, (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 0.69/0.89      inference('sat_resolution*', [status(thm)], ['7', '17'])).
% 0.69/0.89  thf('19', plain, (((sk_A) != (k2_tarski @ sk_B @ sk_C))),
% 0.69/0.89      inference('simpl_trail', [status(thm)], ['6', '18'])).
% 0.69/0.89  thf('20', plain,
% 0.69/0.89      ((((sk_A) = (k1_tarski @ sk_C))
% 0.69/0.89        | ((sk_A) = (k1_tarski @ sk_B))
% 0.69/0.89        | ((sk_A) = (k1_xboole_0))
% 0.69/0.89        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.69/0.89      inference('simplify_reflect-', [status(thm)], ['4', '19'])).
% 0.69/0.89  thf('21', plain,
% 0.69/0.89      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('split', [status(esa)], ['2'])).
% 0.69/0.89  thf('22', plain,
% 0.69/0.89      (((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.89         | ((sk_A) = (k1_xboole_0))
% 0.69/0.89         | ((sk_A) = (k1_tarski @ sk_B))
% 0.69/0.89         | ((sk_A) = (k1_tarski @ sk_C))))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['20', '21'])).
% 0.69/0.89  thf('23', plain,
% 0.69/0.89      (((((sk_A) = (k1_tarski @ sk_C))
% 0.69/0.89         | ((sk_A) = (k1_tarski @ sk_B))
% 0.69/0.89         | ((sk_A) = (k1_xboole_0))))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('simplify', [status(thm)], ['22'])).
% 0.69/0.89  thf(t31_zfmisc_1, axiom,
% 0.69/0.89    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.69/0.89  thf('24', plain, (![X43 : $i]: ((k3_tarski @ (k1_tarski @ X43)) = (X43))),
% 0.69/0.89      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.69/0.89  thf('25', plain,
% 0.69/0.89      (((((k3_tarski @ sk_A) = (sk_C))
% 0.69/0.89         | ((sk_A) = (k1_xboole_0))
% 0.69/0.89         | ((sk_A) = (k1_tarski @ sk_B))))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('sup+', [status(thm)], ['23', '24'])).
% 0.69/0.89  thf(t42_zfmisc_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i]:
% 0.69/0.89     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.69/0.89       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.69/0.89            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.69/0.89  thf('26', plain,
% 0.69/0.89      (![X44 : $i, X46 : $i, X47 : $i]:
% 0.69/0.89         ((r1_tarski @ X46 @ (k2_tarski @ X44 @ X47))
% 0.69/0.89          | ((X46) != (k1_tarski @ X44)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t42_zfmisc_1])).
% 0.69/0.89  thf('27', plain,
% 0.69/0.89      (![X44 : $i, X47 : $i]:
% 0.69/0.89         (r1_tarski @ (k1_tarski @ X44) @ (k2_tarski @ X44 @ X47))),
% 0.69/0.89      inference('simplify', [status(thm)], ['26'])).
% 0.69/0.89  thf(t45_xboole_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( r1_tarski @ A @ B ) =>
% 0.69/0.89       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.69/0.89  thf('28', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i]:
% 0.69/0.89         (((X6) = (k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5)))
% 0.69/0.89          | ~ (r1_tarski @ X5 @ X6))),
% 0.69/0.89      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.69/0.89  thf(t39_xboole_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.69/0.89  thf('29', plain,
% 0.69/0.89      (![X3 : $i, X4 : $i]:
% 0.69/0.89         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.69/0.89           = (k2_xboole_0 @ X3 @ X4))),
% 0.69/0.89      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.69/0.89  thf('30', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i]:
% 0.69/0.89         (((X6) = (k2_xboole_0 @ X5 @ X6)) | ~ (r1_tarski @ X5 @ X6))),
% 0.69/0.89      inference('demod', [status(thm)], ['28', '29'])).
% 0.69/0.89  thf('31', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k2_tarski @ X1 @ X0)
% 0.69/0.89           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['27', '30'])).
% 0.69/0.89  thf(t7_xboole_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.69/0.89  thf('32', plain,
% 0.69/0.89      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.69/0.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.69/0.89  thf('33', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i]:
% 0.69/0.89         (((X6) = (k2_xboole_0 @ X5 @ X6)) | ~ (r1_tarski @ X5 @ X6))),
% 0.69/0.89      inference('demod', [status(thm)], ['28', '29'])).
% 0.69/0.89  thf('34', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k2_xboole_0 @ X1 @ X0)
% 0.69/0.89           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['32', '33'])).
% 0.69/0.89  thf(t95_xboole_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( k3_xboole_0 @ A @ B ) =
% 0.69/0.89       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.69/0.89  thf('35', plain,
% 0.69/0.89      (![X14 : $i, X15 : $i]:
% 0.69/0.89         ((k3_xboole_0 @ X14 @ X15)
% 0.69/0.89           = (k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 0.69/0.89              (k2_xboole_0 @ X14 @ X15)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.69/0.89  thf(t91_xboole_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i]:
% 0.69/0.89     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.69/0.89       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.69/0.89  thf('36', plain,
% 0.69/0.89      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.69/0.89         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.69/0.89           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.69/0.89  thf('37', plain,
% 0.69/0.89      (![X14 : $i, X15 : $i]:
% 0.69/0.89         ((k3_xboole_0 @ X14 @ X15)
% 0.69/0.89           = (k5_xboole_0 @ X14 @ 
% 0.69/0.89              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 0.69/0.89      inference('demod', [status(thm)], ['35', '36'])).
% 0.69/0.89  thf('38', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.69/0.89           = (k5_xboole_0 @ X1 @ 
% 0.69/0.89              (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))))),
% 0.69/0.89      inference('sup+', [status(thm)], ['34', '37'])).
% 0.69/0.89  thf('39', plain,
% 0.69/0.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['9', '10'])).
% 0.69/0.89  thf('40', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.69/0.89      inference('demod', [status(thm)], ['8', '11'])).
% 0.69/0.89  thf('41', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.69/0.89           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.69/0.89      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.69/0.89  thf(t5_boole, axiom,
% 0.69/0.89    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.69/0.89  thf('42', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.69/0.89      inference('cnf', [status(esa)], [t5_boole])).
% 0.69/0.89  thf('43', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.69/0.89      inference('demod', [status(thm)], ['41', '42'])).
% 0.69/0.89  thf('44', plain,
% 0.69/0.89      (![X1 : $i, X2 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ X1 @ X2)
% 0.69/0.89           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.69/0.89  thf('45', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.69/0.89           = (k5_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['43', '44'])).
% 0.69/0.89  thf('46', plain,
% 0.69/0.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['9', '10'])).
% 0.69/0.89  thf('47', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.69/0.89           = (k4_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['45', '46'])).
% 0.69/0.89  thf('48', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.69/0.89           = (k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X1)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['31', '47'])).
% 0.69/0.89  thf('49', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.69/0.89      inference('demod', [status(thm)], ['8', '11'])).
% 0.69/0.89  thf('50', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.69/0.89           = (k1_xboole_0))),
% 0.69/0.89      inference('demod', [status(thm)], ['48', '49'])).
% 0.69/0.89  thf('51', plain,
% 0.69/0.89      ((![X0 : $i]:
% 0.69/0.89          (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ X0)) = (k1_xboole_0))
% 0.69/0.89           | ((sk_A) = (k1_xboole_0))
% 0.69/0.89           | ((k3_tarski @ sk_A) = (sk_C))))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('sup+', [status(thm)], ['25', '50'])).
% 0.69/0.89  thf('52', plain,
% 0.69/0.89      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('split', [status(esa)], ['2'])).
% 0.69/0.89  thf('53', plain,
% 0.69/0.89      (((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.89         | ((k3_tarski @ sk_A) = (sk_C))
% 0.69/0.89         | ((sk_A) = (k1_xboole_0))))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['51', '52'])).
% 0.69/0.89  thf('54', plain,
% 0.69/0.89      (((((sk_A) = (k1_xboole_0)) | ((k3_tarski @ sk_A) = (sk_C))))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('simplify', [status(thm)], ['53'])).
% 0.69/0.89  thf('55', plain,
% 0.69/0.89      (((((sk_A) = (k1_tarski @ sk_C))
% 0.69/0.89         | ((sk_A) = (k1_tarski @ sk_B))
% 0.69/0.89         | ((sk_A) = (k1_xboole_0))))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('simplify', [status(thm)], ['22'])).
% 0.69/0.89  thf('56', plain,
% 0.69/0.89      (![X44 : $i, X46 : $i, X47 : $i]:
% 0.69/0.89         ((r1_tarski @ X46 @ (k2_tarski @ X44 @ X47))
% 0.69/0.89          | ((X46) != (k1_tarski @ X47)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t42_zfmisc_1])).
% 0.69/0.89  thf('57', plain,
% 0.69/0.89      (![X44 : $i, X47 : $i]:
% 0.69/0.89         (r1_tarski @ (k1_tarski @ X47) @ (k2_tarski @ X44 @ X47))),
% 0.69/0.89      inference('simplify', [status(thm)], ['56'])).
% 0.69/0.89  thf('58', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i]:
% 0.69/0.89         (((X6) = (k2_xboole_0 @ X5 @ X6)) | ~ (r1_tarski @ X5 @ X6))),
% 0.69/0.89      inference('demod', [status(thm)], ['28', '29'])).
% 0.69/0.89  thf('59', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k2_tarski @ X1 @ X0)
% 0.69/0.89           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['57', '58'])).
% 0.69/0.89  thf('60', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.69/0.89           = (k4_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['45', '46'])).
% 0.69/0.89  thf('61', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.69/0.89           = (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['59', '60'])).
% 0.69/0.89  thf('62', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.69/0.89      inference('demod', [status(thm)], ['8', '11'])).
% 0.69/0.89  thf('63', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.69/0.89           = (k1_xboole_0))),
% 0.69/0.89      inference('demod', [status(thm)], ['61', '62'])).
% 0.69/0.89  thf('64', plain,
% 0.69/0.89      ((![X0 : $i]:
% 0.69/0.89          (((k4_xboole_0 @ sk_A @ (k2_tarski @ X0 @ sk_C)) = (k1_xboole_0))
% 0.69/0.89           | ((sk_A) = (k1_xboole_0))
% 0.69/0.89           | ((sk_A) = (k1_tarski @ sk_B))))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('sup+', [status(thm)], ['55', '63'])).
% 0.69/0.89  thf('65', plain,
% 0.69/0.89      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('split', [status(esa)], ['2'])).
% 0.69/0.89  thf('66', plain,
% 0.69/0.89      (((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.89         | ((sk_A) = (k1_tarski @ sk_B))
% 0.69/0.89         | ((sk_A) = (k1_xboole_0))))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['64', '65'])).
% 0.69/0.89  thf('67', plain,
% 0.69/0.89      (((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B))))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('simplify', [status(thm)], ['66'])).
% 0.69/0.89  thf('68', plain, (![X43 : $i]: ((k3_tarski @ (k1_tarski @ X43)) = (X43))),
% 0.69/0.89      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.69/0.89  thf('69', plain,
% 0.69/0.89      (((((k3_tarski @ sk_A) = (sk_B)) | ((sk_A) = (k1_xboole_0))))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('sup+', [status(thm)], ['67', '68'])).
% 0.69/0.89  thf('70', plain,
% 0.69/0.89      (((((sk_C) = (sk_B))
% 0.69/0.89         | ((sk_A) = (k1_xboole_0))
% 0.69/0.89         | ((sk_A) = (k1_xboole_0))))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('sup+', [status(thm)], ['54', '69'])).
% 0.69/0.89  thf('71', plain,
% 0.69/0.89      (((((sk_A) = (k1_xboole_0)) | ((sk_C) = (sk_B))))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('simplify', [status(thm)], ['70'])).
% 0.69/0.89  thf('72', plain, (((sk_A) != (k2_tarski @ sk_B @ sk_C))),
% 0.69/0.89      inference('simpl_trail', [status(thm)], ['6', '18'])).
% 0.69/0.89  thf('73', plain,
% 0.69/0.89      (((((sk_A) != (k2_tarski @ sk_B @ sk_B)) | ((sk_A) = (k1_xboole_0))))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['71', '72'])).
% 0.69/0.89  thf(t69_enumset1, axiom,
% 0.69/0.89    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.69/0.89  thf('74', plain,
% 0.69/0.89      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.69/0.89      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.69/0.89  thf('75', plain,
% 0.69/0.89      (((((sk_A) != (k1_tarski @ sk_B)) | ((sk_A) = (k1_xboole_0))))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('demod', [status(thm)], ['73', '74'])).
% 0.69/0.89  thf('76', plain,
% 0.69/0.89      (((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B))))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('simplify', [status(thm)], ['66'])).
% 0.69/0.89  thf('77', plain,
% 0.69/0.89      ((((sk_A) = (k1_xboole_0)))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('clc', [status(thm)], ['75', '76'])).
% 0.69/0.89  thf('78', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.69/0.89      inference('demod', [status(thm)], ['8', '11'])).
% 0.69/0.89  thf('79', plain,
% 0.69/0.89      (![X14 : $i, X15 : $i]:
% 0.69/0.89         ((k3_xboole_0 @ X14 @ X15)
% 0.69/0.89           = (k5_xboole_0 @ X14 @ 
% 0.69/0.89              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 0.69/0.89      inference('demod', [status(thm)], ['35', '36'])).
% 0.69/0.89  thf('80', plain,
% 0.69/0.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['9', '10'])).
% 0.69/0.89  thf('81', plain,
% 0.69/0.89      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.69/0.89         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.69/0.89           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.69/0.89  thf('82', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.69/0.89           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['80', '81'])).
% 0.69/0.89  thf('83', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k2_xboole_0 @ X0 @ X0))
% 0.69/0.89           = (k3_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['79', '82'])).
% 0.69/0.89  thf('84', plain,
% 0.69/0.89      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.69/0.89      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.69/0.89  thf(l51_zfmisc_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.69/0.89  thf('85', plain,
% 0.69/0.89      (![X41 : $i, X42 : $i]:
% 0.69/0.89         ((k3_tarski @ (k2_tarski @ X41 @ X42)) = (k2_xboole_0 @ X41 @ X42))),
% 0.69/0.89      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.69/0.89  thf('86', plain,
% 0.69/0.89      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['84', '85'])).
% 0.69/0.89  thf('87', plain, (![X43 : $i]: ((k3_tarski @ (k1_tarski @ X43)) = (X43))),
% 0.69/0.89      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.69/0.89  thf('88', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['86', '87'])).
% 0.69/0.89  thf('89', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.69/0.89      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.69/0.89  thf('90', plain,
% 0.69/0.89      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['83', '88', '89'])).
% 0.69/0.89  thf('91', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['78', '90'])).
% 0.69/0.89  thf('92', plain,
% 0.69/0.89      (![X1 : $i, X2 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ X1 @ X2)
% 0.69/0.89           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.69/0.89  thf('93', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['91', '92'])).
% 0.69/0.89  thf('94', plain,
% 0.69/0.89      (![X44 : $i, X46 : $i, X47 : $i]:
% 0.69/0.89         ((r1_tarski @ X46 @ (k2_tarski @ X44 @ X47))
% 0.69/0.89          | ((X46) != (k1_xboole_0)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t42_zfmisc_1])).
% 0.69/0.89  thf('95', plain,
% 0.69/0.89      (![X44 : $i, X47 : $i]:
% 0.69/0.89         (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X44 @ X47))),
% 0.69/0.89      inference('simplify', [status(thm)], ['94'])).
% 0.69/0.89  thf('96', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i]:
% 0.69/0.89         (((X6) = (k2_xboole_0 @ X5 @ X6)) | ~ (r1_tarski @ X5 @ X6))),
% 0.69/0.89      inference('demod', [status(thm)], ['28', '29'])).
% 0.69/0.89  thf('97', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k2_tarski @ X1 @ X0)
% 0.69/0.89           = (k2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X1 @ X0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['95', '96'])).
% 0.69/0.89  thf('98', plain,
% 0.69/0.89      (![X14 : $i, X15 : $i]:
% 0.69/0.89         ((k3_xboole_0 @ X14 @ X15)
% 0.69/0.89           = (k5_xboole_0 @ X14 @ 
% 0.69/0.89              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 0.69/0.89      inference('demod', [status(thm)], ['35', '36'])).
% 0.69/0.89  thf('99', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k3_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X1 @ X0))
% 0.69/0.89           = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.69/0.89              (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X1 @ X0))))),
% 0.69/0.89      inference('sup+', [status(thm)], ['97', '98'])).
% 0.69/0.89  thf('100', plain,
% 0.69/0.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['9', '10'])).
% 0.69/0.89  thf('101', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.69/0.89      inference('demod', [status(thm)], ['8', '11'])).
% 0.69/0.89  thf('102', plain,
% 0.69/0.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['9', '10'])).
% 0.69/0.89  thf('103', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.69/0.89      inference('demod', [status(thm)], ['8', '11'])).
% 0.69/0.89  thf('104', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k3_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X1 @ X0)) = (k1_xboole_0))),
% 0.69/0.89      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 0.69/0.89  thf('105', plain,
% 0.69/0.89      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.69/0.89      inference('demod', [status(thm)], ['3', '77', '93', '104'])).
% 0.69/0.89  thf('106', plain,
% 0.69/0.89      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.69/0.89      inference('simplify', [status(thm)], ['105'])).
% 0.69/0.89  thf('107', plain,
% 0.69/0.89      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.69/0.89      inference('sat_resolution*', [status(thm)], ['106'])).
% 0.69/0.89  thf('108', plain,
% 0.69/0.89      (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.69/0.89      inference('simpl_trail', [status(thm)], ['1', '107'])).
% 0.69/0.89  thf('109', plain,
% 0.69/0.89      (![X14 : $i, X15 : $i]:
% 0.69/0.89         ((k3_xboole_0 @ X14 @ X15)
% 0.69/0.89           = (k5_xboole_0 @ X14 @ 
% 0.69/0.89              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 0.69/0.89      inference('demod', [status(thm)], ['35', '36'])).
% 0.69/0.89  thf('110', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.69/0.89           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['80', '81'])).
% 0.69/0.89  thf('111', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.69/0.89      inference('demod', [status(thm)], ['8', '11'])).
% 0.69/0.89  thf('112', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.69/0.89      inference('demod', [status(thm)], ['8', '11'])).
% 0.69/0.89  thf('113', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X1 @ X1) = (k4_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['111', '112'])).
% 0.69/0.89  thf('114', plain,
% 0.69/0.89      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['83', '88', '89'])).
% 0.69/0.89  thf('115', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.69/0.89      inference('sup+', [status(thm)], ['113', '114'])).
% 0.69/0.89  thf('116', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.69/0.89      inference('demod', [status(thm)], ['110', '115'])).
% 0.69/0.89  thf('117', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.69/0.89           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['109', '116'])).
% 0.69/0.89  thf('118', plain,
% 0.69/0.89      (![X1 : $i, X2 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ X1 @ X2)
% 0.69/0.89           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.69/0.89  thf('119', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.69/0.89           = (k4_xboole_0 @ X1 @ X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['117', '118'])).
% 0.69/0.89  thf('120', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.69/0.89      inference('demod', [status(thm)], ['110', '115'])).
% 0.69/0.89  thf('121', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k2_xboole_0 @ X1 @ X0)
% 0.69/0.89           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['119', '120'])).
% 0.69/0.89  thf('122', plain,
% 0.69/0.89      (((k2_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C))
% 0.69/0.89         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['108', '121'])).
% 0.69/0.89  thf('123', plain,
% 0.69/0.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['9', '10'])).
% 0.69/0.89  thf('124', plain,
% 0.69/0.89      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.69/0.89         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.69/0.89           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.69/0.89  thf('125', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.69/0.89           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.69/0.89      inference('sup+', [status(thm)], ['123', '124'])).
% 0.69/0.89  thf('126', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.69/0.89      inference('demod', [status(thm)], ['8', '11'])).
% 0.69/0.89  thf('127', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k1_xboole_0)
% 0.69/0.89           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.69/0.89      inference('demod', [status(thm)], ['125', '126'])).
% 0.69/0.89  thf('128', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.69/0.89      inference('demod', [status(thm)], ['110', '115'])).
% 0.69/0.89  thf('129', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.69/0.89           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['127', '128'])).
% 0.69/0.89  thf('130', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.69/0.89      inference('cnf', [status(esa)], [t5_boole])).
% 0.69/0.89  thf('131', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.69/0.89      inference('demod', [status(thm)], ['129', '130'])).
% 0.69/0.89  thf('132', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.69/0.89      inference('demod', [status(thm)], ['110', '115'])).
% 0.69/0.89  thf('133', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['131', '132'])).
% 0.69/0.89  thf('134', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['78', '90'])).
% 0.69/0.89  thf('135', plain,
% 0.69/0.89      (((k2_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C))
% 0.69/0.89         = (k2_tarski @ sk_B @ sk_C))),
% 0.69/0.89      inference('demod', [status(thm)], ['122', '133', '134'])).
% 0.69/0.89  thf('136', plain,
% 0.69/0.89      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.69/0.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.69/0.89  thf('137', plain, ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))),
% 0.69/0.89      inference('sup+', [status(thm)], ['135', '136'])).
% 0.69/0.89  thf('138', plain,
% 0.69/0.89      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.69/0.89         (((X46) = (k2_tarski @ X44 @ X45))
% 0.69/0.89          | ((X46) = (k1_tarski @ X45))
% 0.69/0.89          | ((X46) = (k1_tarski @ X44))
% 0.69/0.89          | ((X46) = (k1_xboole_0))
% 0.69/0.89          | ~ (r1_tarski @ X46 @ (k2_tarski @ X44 @ X45)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t42_zfmisc_1])).
% 0.69/0.89  thf('139', plain,
% 0.69/0.89      ((((sk_A) = (k1_xboole_0))
% 0.69/0.89        | ((sk_A) = (k1_tarski @ sk_B))
% 0.69/0.89        | ((sk_A) = (k1_tarski @ sk_C))
% 0.69/0.89        | ((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['137', '138'])).
% 0.69/0.89  thf('140', plain, (((sk_A) != (k2_tarski @ sk_B @ sk_C))),
% 0.69/0.89      inference('simpl_trail', [status(thm)], ['6', '18'])).
% 0.69/0.89  thf('141', plain,
% 0.69/0.89      ((((sk_A) != (k1_tarski @ sk_C))
% 0.69/0.89        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('142', plain,
% 0.69/0.89      ((((sk_A) != (k1_tarski @ sk_C))) <= (~ (((sk_A) = (k1_tarski @ sk_C))))),
% 0.69/0.89      inference('split', [status(esa)], ['141'])).
% 0.69/0.89  thf('143', plain,
% 0.69/0.89      (~ (((sk_A) = (k1_tarski @ sk_C))) | 
% 0.69/0.89       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.69/0.89      inference('split', [status(esa)], ['141'])).
% 0.69/0.89  thf('144', plain, (~ (((sk_A) = (k1_tarski @ sk_C)))),
% 0.69/0.89      inference('sat_resolution*', [status(thm)], ['106', '143'])).
% 0.69/0.89  thf('145', plain, (((sk_A) != (k1_tarski @ sk_C))),
% 0.69/0.89      inference('simpl_trail', [status(thm)], ['142', '144'])).
% 0.69/0.89  thf('146', plain,
% 0.69/0.89      ((((sk_A) != (k1_tarski @ sk_B))
% 0.69/0.89        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('147', plain,
% 0.69/0.89      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.69/0.89      inference('split', [status(esa)], ['146'])).
% 0.69/0.89  thf('148', plain,
% 0.69/0.89      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.69/0.89       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.69/0.89      inference('split', [status(esa)], ['146'])).
% 0.69/0.89  thf('149', plain, (~ (((sk_A) = (k1_tarski @ sk_B)))),
% 0.69/0.89      inference('sat_resolution*', [status(thm)], ['106', '148'])).
% 0.69/0.89  thf('150', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.69/0.89      inference('simpl_trail', [status(thm)], ['147', '149'])).
% 0.69/0.89  thf('151', plain,
% 0.69/0.89      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.69/0.89      inference('split', [status(esa)], ['2'])).
% 0.69/0.89  thf('152', plain,
% 0.69/0.89      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.69/0.89       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.69/0.89      inference('split', [status(esa)], ['2'])).
% 0.69/0.89  thf('153', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.69/0.89      inference('sat_resolution*', [status(thm)], ['106', '152'])).
% 0.69/0.89  thf('154', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.89      inference('simpl_trail', [status(thm)], ['151', '153'])).
% 0.69/0.89  thf('155', plain, ($false),
% 0.69/0.89      inference('simplify_reflect-', [status(thm)],
% 0.69/0.89                ['139', '140', '145', '150', '154'])).
% 0.69/0.89  
% 0.69/0.89  % SZS output end Refutation
% 0.69/0.89  
% 0.69/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j89MBP1KGb

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:40 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 166 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :   18
%              Number of atoms          :  871 (2461 expanded)
%              Number of equality atoms :  166 ( 508 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B_1 @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('5',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('11',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('13',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B_1 @ sk_C ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
     != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B_1 @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_C ) )
   <= ( sk_A
      = ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

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

thf('22',plain,(
    ! [X47: $i,X49: $i,X50: $i] :
      ( ( r1_tarski @ X49 @ ( k2_tarski @ X47 @ X50 ) )
      | ( X49
       != ( k1_tarski @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t42_zfmisc_1])).

thf('23',plain,(
    ! [X47: $i,X50: $i] :
      ( r1_tarski @ ( k1_tarski @ X50 ) @ ( k2_tarski @ X47 @ X50 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_A @ ( k2_tarski @ X0 @ sk_C ) )
   <= ( sk_A
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ X0 @ sk_C ) )
        = k1_xboole_0 )
   <= ( sk_A
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k1_tarski @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B_1 @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B_1 @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('38',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X49
        = ( k2_tarski @ X47 @ X48 ) )
      | ( X49
        = ( k1_tarski @ X48 ) )
      | ( X49
        = ( k1_tarski @ X47 ) )
      | ( X49 = k1_xboole_0 )
      | ~ ( r1_tarski @ X49 @ ( k2_tarski @ X47 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t42_zfmisc_1])).

thf('41',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B_1 ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k2_tarski @ sk_B_1 @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
      = k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('44',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','43'])).

thf('45',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['42','44'])).

thf('46',plain,
    ( ( ( sk_A
        = ( k1_tarski @ sk_B_1 ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k2_tarski @ sk_B_1 @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['41','45'])).

thf('47',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B_1 @ sk_C ) )
   <= ( sk_A
     != ( k2_tarski @ sk_B_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['34'])).

thf('48',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k1_tarski @ sk_B_1 ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B_1 @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( sk_A
        = ( k1_tarski @ sk_B_1 ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B_1 @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
   <= ( sk_A
     != ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['32'])).

thf('51',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A
        = ( k1_tarski @ sk_B_1 ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B_1 @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B_1 @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['30'])).

thf('54',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B_1 @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_B_1 ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k2_tarski @ sk_B_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('57',plain,(
    ! [X47: $i,X49: $i,X50: $i] :
      ( ( r1_tarski @ X49 @ ( k2_tarski @ X47 @ X50 ) )
      | ( X49
       != ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t42_zfmisc_1])).

thf('58',plain,(
    ! [X47: $i,X50: $i] :
      ( r1_tarski @ ( k1_tarski @ X47 ) @ ( k2_tarski @ X47 @ X50 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B_1 @ X0 ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ X0 ) )
        = k1_xboole_0 )
   <= ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
      = k1_xboole_0 )
    | ( sk_A
      = ( k2_tarski @ sk_B_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('66',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','12','20','29','31','33','35','55','64','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j89MBP1KGb
% 0.07/0.25  % Computer   : n025.cluster.edu
% 0.07/0.25  % Model      : x86_64 x86_64
% 0.07/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.25  % Memory     : 8042.1875MB
% 0.07/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.25  % CPULimit   : 60
% 0.07/0.25  % DateTime   : Tue Dec  1 13:50:50 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.26  % Running portfolio for 600 s
% 0.07/0.26  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.07/0.26  % Number of cores: 8
% 0.07/0.26  % Python version: Python 3.6.8
% 0.07/0.26  % Running in FO mode
% 1.07/1.23  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.07/1.23  % Solved by: fo/fo7.sh
% 1.07/1.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.23  % done 3411 iterations in 0.869s
% 1.07/1.23  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.07/1.23  % SZS output start Refutation
% 1.07/1.23  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.07/1.23  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.07/1.23  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.07/1.23  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.07/1.23  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.07/1.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.07/1.23  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.23  thf(sk_C_type, type, sk_C: $i).
% 1.07/1.23  thf(t75_zfmisc_1, conjecture,
% 1.07/1.23    (![A:$i,B:$i,C:$i]:
% 1.07/1.23     ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 1.07/1.23       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 1.07/1.23            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 1.07/1.23  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.23    (~( ![A:$i,B:$i,C:$i]:
% 1.07/1.23        ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 1.07/1.23          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 1.07/1.23               ( ( A ) != ( k1_tarski @ C ) ) & 
% 1.07/1.23               ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ) )),
% 1.07/1.23    inference('cnf.neg', [status(esa)], [t75_zfmisc_1])).
% 1.07/1.23  thf('0', plain,
% 1.07/1.23      ((((sk_A) != (k1_xboole_0))
% 1.07/1.23        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) != (k1_xboole_0)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('1', plain,
% 1.07/1.23      (~ (((sk_A) = (k1_xboole_0))) | 
% 1.07/1.23       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) = (k1_xboole_0)))),
% 1.07/1.23      inference('split', [status(esa)], ['0'])).
% 1.07/1.23  thf('2', plain,
% 1.07/1.23      ((((sk_A) = (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23        | ((sk_A) = (k1_tarski @ sk_C))
% 1.07/1.23        | ((sk_A) = (k1_tarski @ sk_B_1))
% 1.07/1.23        | ((sk_A) = (k1_xboole_0))
% 1.07/1.23        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) = (k1_xboole_0)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('3', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.07/1.23      inference('split', [status(esa)], ['2'])).
% 1.07/1.23  thf(t4_boole, axiom,
% 1.07/1.23    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.07/1.23  thf('4', plain,
% 1.07/1.23      (![X21 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X21) = (k1_xboole_0))),
% 1.07/1.23      inference('cnf', [status(esa)], [t4_boole])).
% 1.07/1.23  thf('5', plain,
% 1.07/1.23      ((![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0)))
% 1.07/1.23         <= ((((sk_A) = (k1_xboole_0))))),
% 1.07/1.23      inference('sup+', [status(thm)], ['3', '4'])).
% 1.07/1.23  thf('6', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.07/1.23      inference('split', [status(esa)], ['2'])).
% 1.07/1.23  thf('7', plain,
% 1.07/1.23      ((![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (sk_A)))
% 1.07/1.23         <= ((((sk_A) = (k1_xboole_0))))),
% 1.07/1.23      inference('demod', [status(thm)], ['5', '6'])).
% 1.07/1.23  thf('8', plain,
% 1.07/1.23      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) != (k1_xboole_0)))
% 1.07/1.23         <= (~
% 1.07/1.23             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))))),
% 1.07/1.23      inference('split', [status(esa)], ['0'])).
% 1.07/1.23  thf('9', plain,
% 1.07/1.23      ((((sk_A) != (k1_xboole_0)))
% 1.07/1.23         <= (~
% 1.07/1.23             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))) & 
% 1.07/1.23             (((sk_A) = (k1_xboole_0))))),
% 1.07/1.23      inference('sup-', [status(thm)], ['7', '8'])).
% 1.07/1.23  thf('10', plain,
% 1.07/1.23      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.07/1.23      inference('split', [status(esa)], ['2'])).
% 1.07/1.23  thf('11', plain,
% 1.07/1.23      ((((sk_A) != (sk_A)))
% 1.07/1.23         <= (~
% 1.07/1.23             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))) & 
% 1.07/1.23             (((sk_A) = (k1_xboole_0))))),
% 1.07/1.23      inference('demod', [status(thm)], ['9', '10'])).
% 1.07/1.23  thf('12', plain,
% 1.07/1.23      (~ (((sk_A) = (k1_xboole_0))) | 
% 1.07/1.23       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) = (k1_xboole_0)))),
% 1.07/1.23      inference('simplify', [status(thm)], ['11'])).
% 1.07/1.23  thf(idempotence_k2_xboole_0, axiom,
% 1.07/1.23    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.07/1.23  thf('13', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 1.07/1.23      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.07/1.23  thf(t46_xboole_1, axiom,
% 1.07/1.23    (![A:$i,B:$i]:
% 1.07/1.23     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.07/1.23  thf('14', plain,
% 1.07/1.23      (![X15 : $i, X16 : $i]:
% 1.07/1.23         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X15 @ X16)) = (k1_xboole_0))),
% 1.07/1.23      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.07/1.23  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.07/1.23      inference('sup+', [status(thm)], ['13', '14'])).
% 1.07/1.23  thf('16', plain,
% 1.07/1.23      ((((sk_A) = (k2_tarski @ sk_B_1 @ sk_C)))
% 1.07/1.23         <= ((((sk_A) = (k2_tarski @ sk_B_1 @ sk_C))))),
% 1.07/1.23      inference('split', [status(esa)], ['2'])).
% 1.07/1.23  thf('17', plain,
% 1.07/1.23      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) != (k1_xboole_0)))
% 1.07/1.23         <= (~
% 1.07/1.23             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))))),
% 1.07/1.23      inference('split', [status(esa)], ['0'])).
% 1.07/1.23  thf('18', plain,
% 1.07/1.23      ((((k4_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0)))
% 1.07/1.23         <= (~
% 1.07/1.23             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))) & 
% 1.07/1.23             (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C))))),
% 1.07/1.23      inference('sup-', [status(thm)], ['16', '17'])).
% 1.07/1.23  thf('19', plain,
% 1.07/1.23      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.07/1.23         <= (~
% 1.07/1.23             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))) & 
% 1.07/1.23             (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C))))),
% 1.07/1.23      inference('sup-', [status(thm)], ['15', '18'])).
% 1.07/1.23  thf('20', plain,
% 1.07/1.23      (~ (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C))) | 
% 1.07/1.23       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) = (k1_xboole_0)))),
% 1.07/1.23      inference('simplify', [status(thm)], ['19'])).
% 1.07/1.23  thf('21', plain,
% 1.07/1.23      ((((sk_A) = (k1_tarski @ sk_C))) <= ((((sk_A) = (k1_tarski @ sk_C))))),
% 1.07/1.23      inference('split', [status(esa)], ['2'])).
% 1.07/1.23  thf(t42_zfmisc_1, axiom,
% 1.07/1.23    (![A:$i,B:$i,C:$i]:
% 1.07/1.23     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 1.07/1.23       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 1.07/1.23            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 1.07/1.23  thf('22', plain,
% 1.07/1.23      (![X47 : $i, X49 : $i, X50 : $i]:
% 1.07/1.23         ((r1_tarski @ X49 @ (k2_tarski @ X47 @ X50))
% 1.07/1.23          | ((X49) != (k1_tarski @ X50)))),
% 1.07/1.23      inference('cnf', [status(esa)], [t42_zfmisc_1])).
% 1.07/1.23  thf('23', plain,
% 1.07/1.23      (![X47 : $i, X50 : $i]:
% 1.07/1.23         (r1_tarski @ (k1_tarski @ X50) @ (k2_tarski @ X47 @ X50))),
% 1.07/1.23      inference('simplify', [status(thm)], ['22'])).
% 1.07/1.23  thf('24', plain,
% 1.07/1.23      ((![X0 : $i]: (r1_tarski @ sk_A @ (k2_tarski @ X0 @ sk_C)))
% 1.07/1.23         <= ((((sk_A) = (k1_tarski @ sk_C))))),
% 1.07/1.23      inference('sup+', [status(thm)], ['21', '23'])).
% 1.07/1.23  thf(l32_xboole_1, axiom,
% 1.07/1.23    (![A:$i,B:$i]:
% 1.07/1.23     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.07/1.23  thf('25', plain,
% 1.07/1.23      (![X4 : $i, X6 : $i]:
% 1.07/1.23         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 1.07/1.23      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.07/1.23  thf('26', plain,
% 1.07/1.23      ((![X0 : $i]:
% 1.07/1.23          ((k4_xboole_0 @ sk_A @ (k2_tarski @ X0 @ sk_C)) = (k1_xboole_0)))
% 1.07/1.23         <= ((((sk_A) = (k1_tarski @ sk_C))))),
% 1.07/1.23      inference('sup-', [status(thm)], ['24', '25'])).
% 1.07/1.23  thf('27', plain,
% 1.07/1.23      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) != (k1_xboole_0)))
% 1.07/1.23         <= (~
% 1.07/1.23             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))))),
% 1.07/1.23      inference('split', [status(esa)], ['0'])).
% 1.07/1.23  thf('28', plain,
% 1.07/1.23      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.07/1.23         <= (~
% 1.07/1.23             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))) & 
% 1.07/1.23             (((sk_A) = (k1_tarski @ sk_C))))),
% 1.07/1.23      inference('sup-', [status(thm)], ['26', '27'])).
% 1.07/1.23  thf('29', plain,
% 1.07/1.23      (~ (((sk_A) = (k1_tarski @ sk_C))) | 
% 1.07/1.23       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) = (k1_xboole_0)))),
% 1.07/1.23      inference('simplify', [status(thm)], ['28'])).
% 1.07/1.23  thf('30', plain,
% 1.07/1.23      ((((sk_A) != (k1_tarski @ sk_B_1))
% 1.07/1.23        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) != (k1_xboole_0)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('31', plain,
% 1.07/1.23      (~ (((sk_A) = (k1_tarski @ sk_B_1))) | 
% 1.07/1.23       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) = (k1_xboole_0)))),
% 1.07/1.23      inference('split', [status(esa)], ['30'])).
% 1.07/1.23  thf('32', plain,
% 1.07/1.23      ((((sk_A) != (k1_tarski @ sk_C))
% 1.07/1.23        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) != (k1_xboole_0)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('33', plain,
% 1.07/1.23      (~ (((sk_A) = (k1_tarski @ sk_C))) | 
% 1.07/1.23       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) = (k1_xboole_0)))),
% 1.07/1.23      inference('split', [status(esa)], ['32'])).
% 1.07/1.23  thf('34', plain,
% 1.07/1.23      ((((sk_A) != (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) != (k1_xboole_0)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('35', plain,
% 1.07/1.23      (~ (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C))) | 
% 1.07/1.23       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) = (k1_xboole_0)))),
% 1.07/1.23      inference('split', [status(esa)], ['34'])).
% 1.07/1.23  thf('36', plain,
% 1.07/1.23      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) = (k1_xboole_0)))
% 1.07/1.23         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))))),
% 1.07/1.23      inference('split', [status(esa)], ['2'])).
% 1.07/1.23  thf('37', plain,
% 1.07/1.23      (![X4 : $i, X5 : $i]:
% 1.07/1.23         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 1.07/1.23      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.07/1.23  thf('38', plain,
% 1.07/1.23      (((((k1_xboole_0) != (k1_xboole_0))
% 1.07/1.23         | (r1_tarski @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))))
% 1.07/1.23         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))))),
% 1.07/1.23      inference('sup-', [status(thm)], ['36', '37'])).
% 1.07/1.23  thf('39', plain,
% 1.07/1.23      (((r1_tarski @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)))
% 1.07/1.23         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))))),
% 1.07/1.23      inference('simplify', [status(thm)], ['38'])).
% 1.07/1.23  thf('40', plain,
% 1.07/1.23      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.07/1.23         (((X49) = (k2_tarski @ X47 @ X48))
% 1.07/1.23          | ((X49) = (k1_tarski @ X48))
% 1.07/1.23          | ((X49) = (k1_tarski @ X47))
% 1.07/1.23          | ((X49) = (k1_xboole_0))
% 1.07/1.23          | ~ (r1_tarski @ X49 @ (k2_tarski @ X47 @ X48)))),
% 1.07/1.23      inference('cnf', [status(esa)], [t42_zfmisc_1])).
% 1.07/1.23  thf('41', plain,
% 1.07/1.23      (((((sk_A) = (k1_xboole_0))
% 1.07/1.23         | ((sk_A) = (k1_tarski @ sk_B_1))
% 1.07/1.23         | ((sk_A) = (k1_tarski @ sk_C))
% 1.07/1.23         | ((sk_A) = (k2_tarski @ sk_B_1 @ sk_C))))
% 1.07/1.23         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))))),
% 1.07/1.23      inference('sup-', [status(thm)], ['39', '40'])).
% 1.07/1.23  thf('42', plain,
% 1.07/1.23      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 1.07/1.23      inference('split', [status(esa)], ['0'])).
% 1.07/1.23  thf('43', plain,
% 1.07/1.23      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) = (k1_xboole_0))) | 
% 1.07/1.23       ~ (((sk_A) = (k1_xboole_0)))),
% 1.07/1.23      inference('simplify', [status(thm)], ['11'])).
% 1.07/1.23  thf('44', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 1.07/1.23      inference('sat_resolution*', [status(thm)], ['1', '43'])).
% 1.07/1.23  thf('45', plain, (((sk_A) != (k1_xboole_0))),
% 1.07/1.23      inference('simpl_trail', [status(thm)], ['42', '44'])).
% 1.07/1.23  thf('46', plain,
% 1.07/1.23      (((((sk_A) = (k1_tarski @ sk_B_1))
% 1.07/1.23         | ((sk_A) = (k1_tarski @ sk_C))
% 1.07/1.23         | ((sk_A) = (k2_tarski @ sk_B_1 @ sk_C))))
% 1.07/1.23         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))))),
% 1.07/1.23      inference('simplify_reflect-', [status(thm)], ['41', '45'])).
% 1.07/1.23  thf('47', plain,
% 1.07/1.23      ((((sk_A) != (k2_tarski @ sk_B_1 @ sk_C)))
% 1.07/1.23         <= (~ (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C))))),
% 1.07/1.23      inference('split', [status(esa)], ['34'])).
% 1.07/1.23  thf('48', plain,
% 1.07/1.23      (((((sk_A) != (sk_A))
% 1.07/1.23         | ((sk_A) = (k1_tarski @ sk_C))
% 1.07/1.23         | ((sk_A) = (k1_tarski @ sk_B_1))))
% 1.07/1.23         <= (~ (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C))) & 
% 1.07/1.23             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))))),
% 1.07/1.23      inference('sup-', [status(thm)], ['46', '47'])).
% 1.07/1.23  thf('49', plain,
% 1.07/1.23      (((((sk_A) = (k1_tarski @ sk_B_1)) | ((sk_A) = (k1_tarski @ sk_C))))
% 1.07/1.23         <= (~ (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C))) & 
% 1.07/1.23             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))))),
% 1.07/1.23      inference('simplify', [status(thm)], ['48'])).
% 1.07/1.23  thf('50', plain,
% 1.07/1.23      ((((sk_A) != (k1_tarski @ sk_C))) <= (~ (((sk_A) = (k1_tarski @ sk_C))))),
% 1.07/1.23      inference('split', [status(esa)], ['32'])).
% 1.07/1.23  thf('51', plain,
% 1.07/1.23      (((((sk_A) != (sk_A)) | ((sk_A) = (k1_tarski @ sk_B_1))))
% 1.07/1.23         <= (~ (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C))) & 
% 1.07/1.23             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 1.07/1.23             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))))),
% 1.07/1.23      inference('sup-', [status(thm)], ['49', '50'])).
% 1.07/1.23  thf('52', plain,
% 1.07/1.23      ((((sk_A) = (k1_tarski @ sk_B_1)))
% 1.07/1.23         <= (~ (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C))) & 
% 1.07/1.23             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 1.07/1.23             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))))),
% 1.07/1.23      inference('simplify', [status(thm)], ['51'])).
% 1.07/1.23  thf('53', plain,
% 1.07/1.23      ((((sk_A) != (k1_tarski @ sk_B_1)))
% 1.07/1.23         <= (~ (((sk_A) = (k1_tarski @ sk_B_1))))),
% 1.07/1.23      inference('split', [status(esa)], ['30'])).
% 1.07/1.23  thf('54', plain,
% 1.07/1.23      ((((sk_A) != (sk_A)))
% 1.07/1.23         <= (~ (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C))) & 
% 1.07/1.23             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 1.07/1.23             ~ (((sk_A) = (k1_tarski @ sk_B_1))) & 
% 1.07/1.23             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))))),
% 1.07/1.23      inference('sup-', [status(thm)], ['52', '53'])).
% 1.07/1.23  thf('55', plain,
% 1.07/1.23      ((((sk_A) = (k1_tarski @ sk_B_1))) | 
% 1.07/1.23       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) = (k1_xboole_0))) | 
% 1.07/1.23       (((sk_A) = (k1_tarski @ sk_C))) | 
% 1.07/1.23       (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C)))),
% 1.07/1.23      inference('simplify', [status(thm)], ['54'])).
% 1.07/1.23  thf('56', plain,
% 1.07/1.23      ((((sk_A) = (k1_tarski @ sk_B_1))) <= ((((sk_A) = (k1_tarski @ sk_B_1))))),
% 1.07/1.23      inference('split', [status(esa)], ['2'])).
% 1.07/1.23  thf('57', plain,
% 1.07/1.23      (![X47 : $i, X49 : $i, X50 : $i]:
% 1.07/1.23         ((r1_tarski @ X49 @ (k2_tarski @ X47 @ X50))
% 1.07/1.23          | ((X49) != (k1_tarski @ X47)))),
% 1.07/1.23      inference('cnf', [status(esa)], [t42_zfmisc_1])).
% 1.07/1.23  thf('58', plain,
% 1.07/1.23      (![X47 : $i, X50 : $i]:
% 1.07/1.23         (r1_tarski @ (k1_tarski @ X47) @ (k2_tarski @ X47 @ X50))),
% 1.07/1.23      inference('simplify', [status(thm)], ['57'])).
% 1.07/1.23  thf('59', plain,
% 1.07/1.23      ((![X0 : $i]: (r1_tarski @ sk_A @ (k2_tarski @ sk_B_1 @ X0)))
% 1.07/1.23         <= ((((sk_A) = (k1_tarski @ sk_B_1))))),
% 1.07/1.23      inference('sup+', [status(thm)], ['56', '58'])).
% 1.07/1.23  thf('60', plain,
% 1.07/1.23      (![X4 : $i, X6 : $i]:
% 1.07/1.23         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 1.07/1.23      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.07/1.23  thf('61', plain,
% 1.07/1.23      ((![X0 : $i]:
% 1.07/1.23          ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ X0)) = (k1_xboole_0)))
% 1.07/1.23         <= ((((sk_A) = (k1_tarski @ sk_B_1))))),
% 1.07/1.23      inference('sup-', [status(thm)], ['59', '60'])).
% 1.07/1.23  thf('62', plain,
% 1.07/1.23      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) != (k1_xboole_0)))
% 1.07/1.23         <= (~
% 1.07/1.23             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))))),
% 1.07/1.23      inference('split', [status(esa)], ['0'])).
% 1.07/1.23  thf('63', plain,
% 1.07/1.23      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.07/1.23         <= (~
% 1.07/1.23             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 1.07/1.23                = (k1_xboole_0))) & 
% 1.07/1.23             (((sk_A) = (k1_tarski @ sk_B_1))))),
% 1.07/1.23      inference('sup-', [status(thm)], ['61', '62'])).
% 1.07/1.23  thf('64', plain,
% 1.07/1.23      (~ (((sk_A) = (k1_tarski @ sk_B_1))) | 
% 1.07/1.23       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) = (k1_xboole_0)))),
% 1.07/1.23      inference('simplify', [status(thm)], ['63'])).
% 1.07/1.23  thf('65', plain,
% 1.07/1.23      ((((sk_A) = (k1_tarski @ sk_B_1))) | (((sk_A) = (k1_tarski @ sk_C))) | 
% 1.07/1.23       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)) = (k1_xboole_0))) | 
% 1.07/1.23       (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C))) | (((sk_A) = (k1_xboole_0)))),
% 1.07/1.23      inference('split', [status(esa)], ['2'])).
% 1.07/1.23  thf('66', plain, ($false),
% 1.07/1.23      inference('sat_resolution*', [status(thm)],
% 1.07/1.23                ['1', '12', '20', '29', '31', '33', '35', '55', '64', '65'])).
% 1.07/1.23  
% 1.07/1.23  % SZS output end Refutation
% 1.07/1.23  
% 1.07/1.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

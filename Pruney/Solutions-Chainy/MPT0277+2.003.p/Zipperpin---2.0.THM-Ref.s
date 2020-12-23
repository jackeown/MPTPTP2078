%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TMCG2xmmDc

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:40 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 325 expanded)
%              Number of leaves         :   17 (  78 expanded)
%              Depth                    :   27
%              Number of atoms          :  890 (4960 expanded)
%              Number of equality atoms :  168 (1029 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C_1 ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
     != k1_xboole_0 )
    | ( sk_A
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
    | ( sk_A
      = ( k1_tarski @ sk_C_1 ) )
    | ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( ( k4_xboole_0 @ X12 @ X13 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('11',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

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

thf('13',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( X60
        = ( k2_tarski @ X58 @ X59 ) )
      | ( X60
        = ( k1_tarski @ X59 ) )
      | ( X60
        = ( k1_tarski @ X58 ) )
      | ( X60 = k1_xboole_0 )
      | ~ ( r1_tarski @ X60 @ ( k2_tarski @ X58 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('14',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B_1 ) )
      | ( sk_A
        = ( k1_tarski @ sk_C_1 ) )
      | ( sk_A
        = ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X28: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X28 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('25',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      = k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['16','26'])).

thf('28',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['15','27'])).

thf('29',plain,
    ( ( ( sk_A
        = ( k1_tarski @ sk_B_1 ) )
      | ( sk_A
        = ( k1_tarski @ sk_C_1 ) )
      | ( sk_A
        = ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['14','28'])).

thf('30',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_A
     != ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('31',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A
        = ( k1_tarski @ sk_C_1 ) )
      | ( sk_A
        = ( k1_tarski @ sk_B_1 ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( sk_A
        = ( k1_tarski @ sk_B_1 ) )
      | ( sk_A
        = ( k1_tarski @ sk_C_1 ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C_1 ) )
   <= ( sk_A
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('34',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A
        = ( k1_tarski @ sk_B_1 ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      & ( sk_A
       != ( k1_tarski @ sk_C_1 ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      & ( sk_A
       != ( k1_tarski @ sk_C_1 ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('37',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      & ( sk_A
       != ( k1_tarski @ sk_C_1 ) )
      & ( sk_A
       != ( k1_tarski @ sk_B_1 ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
     != k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ sk_C_1 ) )
    | ( sk_A
      = ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','5','7','38'])).

thf('40',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','39'])).

thf('41',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_C_1 ) )
   <= ( sk_A
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('42',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('44',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
     != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k5_xboole_0 @ sk_A @ sk_A )
     != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('50',plain,(
    ! [X42: $i] :
      ( ( k5_xboole_0 @ X42 @ X42 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('51',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
     != k1_xboole_0 )
    | ( sk_A
     != ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('54',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('55',plain,(
    ! [X58: $i,X60: $i,X61: $i] :
      ( ( r1_tarski @ X60 @ ( k2_tarski @ X58 @ X61 ) )
      | ( X60
       != ( k1_tarski @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('56',plain,(
    ! [X58: $i,X61: $i] :
      ( r1_tarski @ ( k1_tarski @ X58 ) @ ( k2_tarski @ X58 @ X61 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B_1 @ X0 ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ X0 ) )
        = k1_xboole_0 )
   <= ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','39'])).

thf('61',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_C_1 ) )
    | ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      = k1_xboole_0 )
    | ( sk_A
      = ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('64',plain,
    ( sk_A
    = ( k1_tarski @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['16','42','52','53','5','7','38','62','63'])).

thf('65',plain,
    ( sk_A
    = ( k1_tarski @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['41','64'])).

thf('66',plain,(
    ! [X58: $i,X60: $i,X61: $i] :
      ( ( r1_tarski @ X60 @ ( k2_tarski @ X58 @ X61 ) )
      | ( X60
       != ( k1_tarski @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('67',plain,(
    ! [X58: $i,X61: $i] :
      ( r1_tarski @ ( k1_tarski @ X61 ) @ ( k2_tarski @ X58 @ X61 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ X0 @ sk_C_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['40','70'])).

thf('72',plain,(
    $false ),
    inference(simplify,[status(thm)],['71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TMCG2xmmDc
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:20:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 690 iterations in 0.190s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.64  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.64  thf(t75_zfmisc_1, conjecture,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.64       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.45/0.64            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.64        ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.64          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.45/0.64               ( ( A ) != ( k1_tarski @ C ) ) & 
% 0.45/0.64               ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t75_zfmisc_1])).
% 0.45/0.64  thf('0', plain,
% 0.45/0.64      ((((sk_A) != (k1_xboole_0))
% 0.45/0.64        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64            != (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)) != (k1_xboole_0)))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64                = (k1_xboole_0))))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      ((((sk_A) != (k1_tarski @ sk_B_1))
% 0.45/0.64        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64            != (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (~ (((sk_A) = (k1_tarski @ sk_B_1))) | 
% 0.45/0.64       ~
% 0.45/0.64       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)) = (k1_xboole_0)))),
% 0.45/0.64      inference('split', [status(esa)], ['2'])).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      ((((sk_A) != (k1_tarski @ sk_C_1))
% 0.45/0.64        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64            != (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (~
% 0.45/0.64       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)) = (k1_xboole_0))) | 
% 0.45/0.64       ~ (((sk_A) = (k1_tarski @ sk_C_1)))),
% 0.45/0.64      inference('split', [status(esa)], ['4'])).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      ((((sk_A) != (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64            != (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (~ (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1))) | 
% 0.45/0.64       ~
% 0.45/0.64       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)) = (k1_xboole_0)))),
% 0.45/0.64      inference('split', [status(esa)], ['6'])).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      ((((sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64        | ((sk_A) = (k1_tarski @ sk_C_1))
% 0.45/0.64        | ((sk_A) = (k1_tarski @ sk_B_1))
% 0.45/0.64        | ((sk_A) = (k1_xboole_0))
% 0.45/0.64        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)) = (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)) = (k1_xboole_0)))
% 0.45/0.64         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64                = (k1_xboole_0))))),
% 0.45/0.64      inference('split', [status(esa)], ['8'])).
% 0.45/0.64  thf(t37_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      (![X12 : $i, X13 : $i]:
% 0.45/0.64         ((r1_tarski @ X12 @ X13)
% 0.45/0.64          | ((k4_xboole_0 @ X12 @ X13) != (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (((((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.64         | (r1_tarski @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))))
% 0.45/0.64         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64                = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (((r1_tarski @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)))
% 0.45/0.64         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64                = (k1_xboole_0))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['11'])).
% 0.45/0.64  thf(l45_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.45/0.64       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.45/0.64            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.45/0.64         (((X60) = (k2_tarski @ X58 @ X59))
% 0.45/0.64          | ((X60) = (k1_tarski @ X59))
% 0.45/0.64          | ((X60) = (k1_tarski @ X58))
% 0.45/0.64          | ((X60) = (k1_xboole_0))
% 0.45/0.64          | ~ (r1_tarski @ X60 @ (k2_tarski @ X58 @ X59)))),
% 0.45/0.64      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      (((((sk_A) = (k1_xboole_0))
% 0.45/0.64         | ((sk_A) = (k1_tarski @ sk_B_1))
% 0.45/0.64         | ((sk_A) = (k1_tarski @ sk_C_1))
% 0.45/0.64         | ((sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1))))
% 0.45/0.64         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64                = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.45/0.64       ~
% 0.45/0.64       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)) = (k1_xboole_0)))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('split', [status(esa)], ['8'])).
% 0.45/0.64  thf(t4_boole, axiom,
% 0.45/0.64    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (![X28 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X28) = (k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [t4_boole])).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      ((![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0)))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('split', [status(esa)], ['8'])).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      ((![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (sk_A)))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('demod', [status(thm)], ['19', '20'])).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)) != (k1_xboole_0)))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64                = (k1_xboole_0))))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('23', plain,
% 0.45/0.64      ((((sk_A) != (k1_xboole_0)))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64                = (k1_xboole_0))) & 
% 0.45/0.64             (((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('split', [status(esa)], ['8'])).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      ((((sk_A) != (sk_A)))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64                = (k1_xboole_0))) & 
% 0.45/0.64             (((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('demod', [status(thm)], ['23', '24'])).
% 0.45/0.64  thf('26', plain,
% 0.45/0.64      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)) = (k1_xboole_0))) | 
% 0.45/0.64       ~ (((sk_A) = (k1_xboole_0)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['25'])).
% 0.45/0.64  thf('27', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.45/0.64      inference('sat_resolution*', [status(thm)], ['16', '26'])).
% 0.45/0.64  thf('28', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.64      inference('simpl_trail', [status(thm)], ['15', '27'])).
% 0.45/0.64  thf('29', plain,
% 0.45/0.64      (((((sk_A) = (k1_tarski @ sk_B_1))
% 0.45/0.64         | ((sk_A) = (k1_tarski @ sk_C_1))
% 0.45/0.64         | ((sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1))))
% 0.45/0.64         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64                = (k1_xboole_0))))),
% 0.45/0.64      inference('simplify_reflect-', [status(thm)], ['14', '28'])).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      ((((sk_A) != (k2_tarski @ sk_B_1 @ sk_C_1)))
% 0.45/0.64         <= (~ (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1))))),
% 0.45/0.64      inference('split', [status(esa)], ['6'])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      (((((sk_A) != (sk_A))
% 0.45/0.64         | ((sk_A) = (k1_tarski @ sk_C_1))
% 0.45/0.64         | ((sk_A) = (k1_tarski @ sk_B_1))))
% 0.45/0.64         <= (~ (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1))) & 
% 0.45/0.64             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64                = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.64  thf('32', plain,
% 0.45/0.64      (((((sk_A) = (k1_tarski @ sk_B_1)) | ((sk_A) = (k1_tarski @ sk_C_1))))
% 0.45/0.64         <= (~ (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1))) & 
% 0.45/0.64             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64                = (k1_xboole_0))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['31'])).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      ((((sk_A) != (k1_tarski @ sk_C_1)))
% 0.45/0.64         <= (~ (((sk_A) = (k1_tarski @ sk_C_1))))),
% 0.45/0.64      inference('split', [status(esa)], ['4'])).
% 0.45/0.64  thf('34', plain,
% 0.45/0.64      (((((sk_A) != (sk_A)) | ((sk_A) = (k1_tarski @ sk_B_1))))
% 0.45/0.64         <= (~ (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1))) & 
% 0.45/0.64             ~ (((sk_A) = (k1_tarski @ sk_C_1))) & 
% 0.45/0.64             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64                = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      ((((sk_A) = (k1_tarski @ sk_B_1)))
% 0.45/0.64         <= (~ (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1))) & 
% 0.45/0.64             ~ (((sk_A) = (k1_tarski @ sk_C_1))) & 
% 0.45/0.64             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64                = (k1_xboole_0))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['34'])).
% 0.45/0.64  thf('36', plain,
% 0.45/0.64      ((((sk_A) != (k1_tarski @ sk_B_1)))
% 0.45/0.64         <= (~ (((sk_A) = (k1_tarski @ sk_B_1))))),
% 0.45/0.64      inference('split', [status(esa)], ['2'])).
% 0.45/0.64  thf('37', plain,
% 0.45/0.64      ((((sk_A) != (sk_A)))
% 0.45/0.64         <= (~ (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1))) & 
% 0.45/0.64             ~ (((sk_A) = (k1_tarski @ sk_C_1))) & 
% 0.45/0.64             ~ (((sk_A) = (k1_tarski @ sk_B_1))) & 
% 0.45/0.64             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64                = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      (~
% 0.45/0.64       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)) = (k1_xboole_0))) | 
% 0.45/0.64       (((sk_A) = (k1_tarski @ sk_B_1))) | (((sk_A) = (k1_tarski @ sk_C_1))) | 
% 0.45/0.64       (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['37'])).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      (~
% 0.45/0.64       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)) = (k1_xboole_0)))),
% 0.45/0.64      inference('sat_resolution*', [status(thm)], ['3', '5', '7', '38'])).
% 0.45/0.64  thf('40', plain,
% 0.45/0.64      (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)) != (k1_xboole_0))),
% 0.45/0.64      inference('simpl_trail', [status(thm)], ['1', '39'])).
% 0.45/0.64  thf('41', plain,
% 0.45/0.64      ((((sk_A) = (k1_tarski @ sk_C_1))) <= ((((sk_A) = (k1_tarski @ sk_C_1))))),
% 0.45/0.64      inference('split', [status(esa)], ['8'])).
% 0.45/0.64  thf('42', plain,
% 0.45/0.64      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.45/0.64       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)) = (k1_xboole_0)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['25'])).
% 0.45/0.64  thf(d6_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k5_xboole_0 @ A @ B ) =
% 0.45/0.64       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.45/0.64  thf('43', plain,
% 0.45/0.64      (![X2 : $i, X3 : $i]:
% 0.45/0.64         ((k5_xboole_0 @ X2 @ X3)
% 0.45/0.64           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.45/0.64      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.45/0.64  thf(idempotence_k2_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.45/0.64  thf('44', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ X7) = (X7))),
% 0.45/0.64      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.45/0.64  thf('45', plain,
% 0.45/0.64      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['43', '44'])).
% 0.45/0.64  thf('46', plain,
% 0.45/0.64      ((((sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1)))
% 0.45/0.64         <= ((((sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1))))),
% 0.45/0.64      inference('split', [status(esa)], ['8'])).
% 0.45/0.64  thf('47', plain,
% 0.45/0.64      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)) != (k1_xboole_0)))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64                = (k1_xboole_0))))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('48', plain,
% 0.45/0.64      ((((k4_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0)))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64                = (k1_xboole_0))) & 
% 0.45/0.64             (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.64  thf('49', plain,
% 0.45/0.64      ((((k5_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0)))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64                = (k1_xboole_0))) & 
% 0.45/0.64             (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['45', '48'])).
% 0.45/0.64  thf(t92_xboole_1, axiom,
% 0.45/0.64    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.45/0.64  thf('50', plain, (![X42 : $i]: ((k5_xboole_0 @ X42 @ X42) = (k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.45/0.64  thf('51', plain,
% 0.45/0.64      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.45/0.64                = (k1_xboole_0))) & 
% 0.45/0.64             (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1))))),
% 0.45/0.64      inference('demod', [status(thm)], ['49', '50'])).
% 0.45/0.64  thf('52', plain,
% 0.45/0.64      (~ (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1))) | 
% 0.45/0.64       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)) = (k1_xboole_0)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['51'])).
% 0.45/0.64  thf('53', plain,
% 0.45/0.64      (~
% 0.45/0.64       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)) = (k1_xboole_0))) | 
% 0.45/0.64       ~ (((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.45/0.64      inference('split', [status(esa)], ['2'])).
% 0.45/0.64  thf('54', plain,
% 0.45/0.64      ((((sk_A) = (k1_tarski @ sk_B_1))) <= ((((sk_A) = (k1_tarski @ sk_B_1))))),
% 0.45/0.64      inference('split', [status(esa)], ['8'])).
% 0.45/0.64  thf('55', plain,
% 0.45/0.64      (![X58 : $i, X60 : $i, X61 : $i]:
% 0.45/0.64         ((r1_tarski @ X60 @ (k2_tarski @ X58 @ X61))
% 0.45/0.64          | ((X60) != (k1_tarski @ X58)))),
% 0.45/0.64      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.45/0.64  thf('56', plain,
% 0.45/0.64      (![X58 : $i, X61 : $i]:
% 0.45/0.64         (r1_tarski @ (k1_tarski @ X58) @ (k2_tarski @ X58 @ X61))),
% 0.45/0.64      inference('simplify', [status(thm)], ['55'])).
% 0.45/0.64  thf('57', plain,
% 0.45/0.64      ((![X0 : $i]: (r1_tarski @ sk_A @ (k2_tarski @ sk_B_1 @ X0)))
% 0.45/0.64         <= ((((sk_A) = (k1_tarski @ sk_B_1))))),
% 0.45/0.64      inference('sup+', [status(thm)], ['54', '56'])).
% 0.45/0.64  thf('58', plain,
% 0.45/0.64      (![X12 : $i, X14 : $i]:
% 0.45/0.64         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 0.45/0.64          | ~ (r1_tarski @ X12 @ X14))),
% 0.45/0.64      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.45/0.64  thf('59', plain,
% 0.45/0.64      ((![X0 : $i]:
% 0.45/0.64          ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ X0)) = (k1_xboole_0)))
% 0.45/0.64         <= ((((sk_A) = (k1_tarski @ sk_B_1))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.64  thf('60', plain,
% 0.45/0.64      (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)) != (k1_xboole_0))),
% 0.45/0.64      inference('simpl_trail', [status(thm)], ['1', '39'])).
% 0.45/0.64  thf('61', plain,
% 0.45/0.64      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.45/0.64         <= ((((sk_A) = (k1_tarski @ sk_B_1))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['59', '60'])).
% 0.45/0.64  thf('62', plain, (~ (((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['61'])).
% 0.45/0.64  thf('63', plain,
% 0.45/0.64      ((((sk_A) = (k1_tarski @ sk_C_1))) | (((sk_A) = (k1_tarski @ sk_B_1))) | 
% 0.45/0.64       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1)) = (k1_xboole_0))) | 
% 0.45/0.64       (((sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1))) | (((sk_A) = (k1_xboole_0)))),
% 0.45/0.64      inference('split', [status(esa)], ['8'])).
% 0.45/0.64  thf('64', plain, ((((sk_A) = (k1_tarski @ sk_C_1)))),
% 0.45/0.64      inference('sat_resolution*', [status(thm)],
% 0.45/0.64                ['16', '42', '52', '53', '5', '7', '38', '62', '63'])).
% 0.45/0.64  thf('65', plain, (((sk_A) = (k1_tarski @ sk_C_1))),
% 0.45/0.64      inference('simpl_trail', [status(thm)], ['41', '64'])).
% 0.45/0.64  thf('66', plain,
% 0.45/0.64      (![X58 : $i, X60 : $i, X61 : $i]:
% 0.45/0.64         ((r1_tarski @ X60 @ (k2_tarski @ X58 @ X61))
% 0.45/0.64          | ((X60) != (k1_tarski @ X61)))),
% 0.45/0.64      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.45/0.64  thf('67', plain,
% 0.45/0.64      (![X58 : $i, X61 : $i]:
% 0.45/0.64         (r1_tarski @ (k1_tarski @ X61) @ (k2_tarski @ X58 @ X61))),
% 0.45/0.64      inference('simplify', [status(thm)], ['66'])).
% 0.45/0.64  thf('68', plain,
% 0.45/0.64      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_tarski @ X0 @ sk_C_1))),
% 0.45/0.64      inference('sup+', [status(thm)], ['65', '67'])).
% 0.45/0.64  thf('69', plain,
% 0.45/0.64      (![X12 : $i, X14 : $i]:
% 0.45/0.64         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 0.45/0.64          | ~ (r1_tarski @ X12 @ X14))),
% 0.45/0.64      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.45/0.64  thf('70', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ sk_A @ (k2_tarski @ X0 @ sk_C_1)) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['68', '69'])).
% 0.45/0.64  thf('71', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.45/0.64      inference('demod', [status(thm)], ['40', '70'])).
% 0.45/0.64  thf('72', plain, ($false), inference('simplify', [status(thm)], ['71'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

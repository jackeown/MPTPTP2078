%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fp2r54Jwsi

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 364 expanded)
%              Number of leaves         :   19 ( 103 expanded)
%              Depth                    :   19
%              Number of atoms          :  701 (4651 expanded)
%              Number of equality atoms :  138 (1030 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_C_2
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X60: $i,X61: $i] :
      ( ( X61
        = ( k1_tarski @ X60 ) )
      | ( X61 = k1_xboole_0 )
      | ~ ( r1_tarski @ X61 @ ( k1_tarski @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( sk_B
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','6','22'])).

thf('24',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ ( k2_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('30',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ ( k2_xboole_0 @ X25 @ X26 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('33',plain,(
    ! [X17: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('36',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('37',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('45',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ ( k2_xboole_0 @ X25 @ X26 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('46',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C_2 @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('48',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_C_2 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('50',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = sk_C_2 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('52',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( sk_C_2
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('59',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k5_xboole_0 @ X0 @ sk_B ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('63',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('64',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ sk_B )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','65'])).

thf('67',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('68',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('71',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('72',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['58','71'])).

thf('73',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('74',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['57','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['43','74'])).

thf('76',plain,(
    sk_C_2 != sk_C_2 ),
    inference(demod,[status(thm)],['24','75'])).

thf('77',plain,(
    $false ),
    inference(simplify,[status(thm)],['76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fp2r54Jwsi
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:24:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 514 iterations in 0.128s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.58  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(t43_zfmisc_1, conjecture,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.58          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.58          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.58          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.58        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.58             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.58             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.58             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.20/0.58  thf('0', plain,
% 0.20/0.58      ((((sk_B) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('1', plain,
% 0.20/0.58      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.20/0.58         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      ((((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.20/0.58         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.20/0.58      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.58  thf('4', plain,
% 0.20/0.58      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('5', plain,
% 0.20/0.58      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.20/0.58      inference('split', [status(esa)], ['5'])).
% 0.20/0.58  thf(t7_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 0.20/0.58      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.58  thf('8', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(l3_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.58  thf('9', plain,
% 0.20/0.58      (![X60 : $i, X61 : $i]:
% 0.20/0.58         (((X61) = (k1_tarski @ X60))
% 0.20/0.58          | ((X61) = (k1_xboole_0))
% 0.20/0.58          | ~ (r1_tarski @ X61 @ (k1_tarski @ X60)))),
% 0.20/0.58      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.58  thf('10', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.20/0.58          | ((X0) = (k1_xboole_0))
% 0.20/0.58          | ((X0) = (k1_tarski @ sk_A)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.58  thf('11', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('12', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.20/0.58          | ((X0) = (k1_xboole_0))
% 0.20/0.58          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.20/0.58      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.58  thf('14', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('15', plain,
% 0.20/0.58      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('16', plain,
% 0.20/0.58      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.58      inference('split', [status(esa)], ['15'])).
% 0.20/0.58  thf('17', plain,
% 0.20/0.58      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.20/0.58         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['14', '16'])).
% 0.20/0.58  thf('18', plain,
% 0.20/0.58      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.20/0.58         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['13', '17'])).
% 0.20/0.58  thf('19', plain,
% 0.20/0.58      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.58      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.58  thf('20', plain,
% 0.20/0.58      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('21', plain,
% 0.20/0.58      ((((sk_B) != (sk_B)))
% 0.20/0.58         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.58  thf('22', plain,
% 0.20/0.58      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.20/0.58      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.58  thf('23', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['4', '6', '22'])).
% 0.20/0.58  thf('24', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.20/0.58  thf(commutativity_k5_xboole_0, axiom,
% 0.20/0.58    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.20/0.58  thf('25', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.20/0.58      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.58  thf(t5_boole, axiom,
% 0.20/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.58  thf('26', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.20/0.58      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.58  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.58  thf(t95_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( k3_xboole_0 @ A @ B ) =
% 0.20/0.58       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.20/0.58  thf('28', plain,
% 0.20/0.58      (![X25 : $i, X26 : $i]:
% 0.20/0.58         ((k3_xboole_0 @ X25 @ X26)
% 0.20/0.58           = (k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ 
% 0.20/0.58              (k2_xboole_0 @ X25 @ X26)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.20/0.58  thf(t91_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.58       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.20/0.58  thf('29', plain,
% 0.20/0.58      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.58         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.20/0.58           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.58  thf('30', plain,
% 0.20/0.58      (![X25 : $i, X26 : $i]:
% 0.20/0.58         ((k3_xboole_0 @ X25 @ X26)
% 0.20/0.58           = (k5_xboole_0 @ X25 @ 
% 0.20/0.58              (k5_xboole_0 @ X26 @ (k2_xboole_0 @ X25 @ X26))))),
% 0.20/0.58      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.58  thf('31', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.58           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['27', '30'])).
% 0.20/0.58  thf(t17_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.58  thf('32', plain,
% 0.20/0.58      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 0.20/0.58      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.58  thf(t3_xboole_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.58  thf('33', plain,
% 0.20/0.58      (![X17 : $i]:
% 0.20/0.58         (((X17) = (k1_xboole_0)) | ~ (r1_tarski @ X17 @ k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.58  thf('34', plain,
% 0.20/0.58      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.58  thf('35', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['31', '34'])).
% 0.20/0.58  thf(t92_xboole_1, axiom,
% 0.20/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.58  thf('36', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.58  thf('37', plain,
% 0.20/0.58      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.58         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.20/0.58           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.58  thf('38', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.58           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.58  thf('39', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.58  thf('40', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.58  thf('41', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['35', '40'])).
% 0.20/0.58  thf('42', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.20/0.58      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.58  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.58  thf('44', plain,
% 0.20/0.58      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.58  thf('45', plain,
% 0.20/0.58      (![X25 : $i, X26 : $i]:
% 0.20/0.58         ((k3_xboole_0 @ X25 @ X26)
% 0.20/0.58           = (k5_xboole_0 @ X25 @ 
% 0.20/0.58              (k5_xboole_0 @ X26 @ (k2_xboole_0 @ X25 @ X26))))),
% 0.20/0.58      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.58  thf('46', plain,
% 0.20/0.58      ((((k3_xboole_0 @ sk_B @ sk_C_2)
% 0.20/0.58          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C_2 @ sk_B)))
% 0.20/0.58        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['44', '45'])).
% 0.20/0.58  thf('47', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.20/0.58      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.58  thf('48', plain,
% 0.20/0.58      ((((k3_xboole_0 @ sk_B @ sk_C_2)
% 0.20/0.58          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_C_2)))
% 0.20/0.58        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.58  thf('49', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.58  thf('50', plain,
% 0.20/0.58      ((((k3_xboole_0 @ sk_B @ sk_C_2) = (sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.58  thf('51', plain,
% 0.20/0.58      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 0.20/0.58      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.58  thf('52', plain, (((r1_tarski @ sk_C_2 @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['50', '51'])).
% 0.20/0.58  thf('53', plain,
% 0.20/0.58      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.58  thf('54', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.20/0.58          | ((X0) = (k1_xboole_0))
% 0.20/0.58          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.20/0.58      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.58  thf('55', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (r1_tarski @ X0 @ sk_B)
% 0.20/0.58          | ((sk_B) = (k1_xboole_0))
% 0.20/0.58          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.20/0.58          | ((X0) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.58  thf('56', plain,
% 0.20/0.58      ((((sk_B) = (k1_xboole_0))
% 0.20/0.58        | ((sk_C_2) = (k1_xboole_0))
% 0.20/0.58        | ((sk_C_2) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.20/0.58        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['52', '55'])).
% 0.20/0.58  thf('57', plain,
% 0.20/0.58      ((((sk_C_2) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.20/0.58        | ((sk_C_2) = (k1_xboole_0))
% 0.20/0.58        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.58      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.58  thf('58', plain,
% 0.20/0.58      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.20/0.58      inference('split', [status(esa)], ['15'])).
% 0.20/0.58  thf('59', plain,
% 0.20/0.58      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.58      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.58  thf('60', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['35', '40'])).
% 0.20/0.58  thf('61', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ sk_B)))
% 0.20/0.58         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['59', '60'])).
% 0.20/0.58  thf('62', plain,
% 0.20/0.58      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.58      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.58  thf('63', plain,
% 0.20/0.58      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.58      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.58  thf('64', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.20/0.58      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.58  thf('65', plain,
% 0.20/0.58      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ sk_B) = (X0)))
% 0.20/0.58         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['63', '64'])).
% 0.20/0.58  thf('66', plain,
% 0.20/0.58      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.20/0.58         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.58      inference('demod', [status(thm)], ['61', '62', '65'])).
% 0.20/0.58  thf('67', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.20/0.58  thf('68', plain,
% 0.20/0.58      ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.58  thf('69', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.20/0.58      inference('simplify', [status(thm)], ['68'])).
% 0.20/0.58  thf('70', plain,
% 0.20/0.58      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.20/0.58      inference('split', [status(esa)], ['15'])).
% 0.20/0.58  thf('71', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 0.20/0.58  thf('72', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['58', '71'])).
% 0.20/0.58  thf('73', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.20/0.58  thf('74', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['57', '72', '73'])).
% 0.20/0.58  thf('75', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0))),
% 0.20/0.58      inference('demod', [status(thm)], ['43', '74'])).
% 0.20/0.58  thf('76', plain, (((sk_C_2) != (sk_C_2))),
% 0.20/0.58      inference('demod', [status(thm)], ['24', '75'])).
% 0.20/0.58  thf('77', plain, ($false), inference('simplify', [status(thm)], ['76'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.20/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

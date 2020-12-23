%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6tBzHVvfbl

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 377 expanded)
%              Number of leaves         :   11 (  88 expanded)
%              Depth                    :   22
%              Number of atoms          :  903 (5815 expanded)
%              Number of equality atoms :  165 (1171 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
     != ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
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

thf('9',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X6
        = ( k2_tarski @ X4 @ X5 ) )
      | ( X6
        = ( k1_tarski @ X5 ) )
      | ( X6
        = ( k1_tarski @ X4 ) )
      | ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('14',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('16',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ ( k2_tarski @ X4 @ X7 ) )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('21',plain,(
    ! [X4: $i,X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X4 @ X7 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['19','28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['18','29'])).

thf('31',plain,
    ( ( ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','30'])).

thf('32',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
   <= ( sk_A
     != ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('33',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('36',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','5','7','37'])).

thf('39',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','38'])).

thf('40',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_C ) )
   <= ( sk_A
      = ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['8'])).

thf('41',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('42',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['8'])).

thf('43',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ ( k2_tarski @ X4 @ X7 ) )
      | ( X6
       != ( k2_tarski @ X4 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('44',plain,(
    ! [X4: $i,X7: $i] :
      ( r1_tarski @ ( k2_tarski @ X4 @ X7 ) @ ( k2_tarski @ X4 @ X7 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['42','44'])).

thf('46',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['8'])).

thf('47',plain,
    ( ( r1_tarski @ sk_A @ sk_A )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('49',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['8'])).

thf('51',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
     != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','5','7','37'])).

thf('54',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
     != k1_xboole_0 )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['52','53'])).

thf('55',plain,(
    sk_A
 != ( k2_tarski @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['49','54'])).

thf('56',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('57',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('58',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ ( k2_tarski @ X4 @ X7 ) )
      | ( X6
       != ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('59',plain,(
    ! [X4: $i,X7: $i] :
      ( r1_tarski @ ( k1_tarski @ X4 ) @ ( k2_tarski @ X4 @ X7 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ X0 ) )
        = k1_xboole_0 )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['57','61'])).

thf('63',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','38'])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('67',plain,
    ( sk_A
    = ( k1_tarski @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['19','41','55','3','5','7','56','65','66'])).

thf('68',plain,
    ( sk_A
    = ( k1_tarski @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['40','67'])).

thf('69',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ ( k2_tarski @ X4 @ X7 ) )
      | ( X6
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('70',plain,(
    ! [X4: $i,X7: $i] :
      ( r1_tarski @ ( k1_tarski @ X7 ) @ ( k2_tarski @ X4 @ X7 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ X0 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','72'])).

thf('74',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['39','73'])).

thf('75',plain,(
    $false ),
    inference(simplify,[status(thm)],['74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6tBzHVvfbl
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:41:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 147 iterations in 0.025s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(t75_zfmisc_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.47       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.20/0.47            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.47        ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.47          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.20/0.47               ( ( A ) != ( k1_tarski @ C ) ) & 
% 0.20/0.47               ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t75_zfmisc_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((((sk_A) != (k1_xboole_0))
% 0.20/0.47        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((((sk_A) != (k1_tarski @ sk_B))
% 0.20/0.47        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.20/0.47       ~ (((sk_A) = (k1_tarski @ sk_B)))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      ((((sk_A) != (k1_tarski @ sk_C))
% 0.20/0.47        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.20/0.47       ~ (((sk_A) = (k1_tarski @ sk_C)))),
% 0.20/0.47      inference('split', [status(esa)], ['4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((((sk_A) != (k2_tarski @ sk_B @ sk_C))
% 0.20/0.47        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.20/0.47       ~ (((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 0.20/0.47      inference('split', [status(esa)], ['6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      ((((sk_A) = (k2_tarski @ sk_B @ sk_C))
% 0.20/0.47        | ((sk_A) = (k1_tarski @ sk_C))
% 0.20/0.47        | ((sk_A) = (k1_tarski @ sk_B))
% 0.20/0.47        | ((sk_A) = (k1_xboole_0))
% 0.20/0.47        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))
% 0.20/0.47         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.20/0.47      inference('split', [status(esa)], ['8'])).
% 0.20/0.47  thf(l32_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.47         | (r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))))
% 0.20/0.47         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))
% 0.20/0.47         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.47  thf(l45_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.20/0.47       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.20/0.47            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         (((X6) = (k2_tarski @ X4 @ X5))
% 0.20/0.47          | ((X6) = (k1_tarski @ X5))
% 0.20/0.47          | ((X6) = (k1_tarski @ X4))
% 0.20/0.47          | ((X6) = (k1_xboole_0))
% 0.20/0.47          | ~ (r1_tarski @ X6 @ (k2_tarski @ X4 @ X5)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (((((sk_A) = (k1_xboole_0))
% 0.20/0.47         | ((sk_A) = (k1_tarski @ sk_B))
% 0.20/0.47         | ((sk_A) = (k1_tarski @ sk_C))
% 0.20/0.47         | ((sk_A) = (k2_tarski @ sk_B @ sk_C))))
% 0.20/0.47         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      ((((sk_A) != (k2_tarski @ sk_B @ sk_C)))
% 0.20/0.47         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.20/0.47      inference('split', [status(esa)], ['6'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (((((sk_A) != (sk_A))
% 0.20/0.47         | ((sk_A) = (k1_tarski @ sk_C))
% 0.20/0.47         | ((sk_A) = (k1_tarski @ sk_B))
% 0.20/0.47         | ((sk_A) = (k1_xboole_0))))
% 0.20/0.47         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.20/0.47             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (((((sk_A) = (k1_xboole_0))
% 0.20/0.47         | ((sk_A) = (k1_tarski @ sk_B))
% 0.20/0.47         | ((sk_A) = (k1_tarski @ sk_C))))
% 0.20/0.47         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.20/0.47             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.20/0.47       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.20/0.47         ((r1_tarski @ X6 @ (k2_tarski @ X4 @ X7)) | ((X6) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X4 : $i, X7 : $i]: (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X4 @ X7))),
% 0.20/0.47      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X0 : $i, X2 : $i]:
% 0.20/0.47         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k4_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X1 @ X0)) = (k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('split', [status(esa)], ['8'])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      ((((k4_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_B @ sk_C))
% 0.20/0.47          != (k1_xboole_0)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.20/0.47             (((sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.20/0.47             (((sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['23', '26'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.20/0.47       ~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.47  thf('29', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['19', '28'])).
% 0.20/0.47  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['18', '29'])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (((((sk_A) = (k1_tarski @ sk_B)) | ((sk_A) = (k1_tarski @ sk_C))))
% 0.20/0.47         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.20/0.47             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['17', '30'])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      ((((sk_A) != (k1_tarski @ sk_C))) <= (~ (((sk_A) = (k1_tarski @ sk_C))))),
% 0.20/0.47      inference('split', [status(esa)], ['4'])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (((((sk_A) != (sk_A)) | ((sk_A) = (k1_tarski @ sk_B))))
% 0.20/0.47         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.20/0.47             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.20/0.47             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      ((((sk_A) = (k1_tarski @ sk_B)))
% 0.20/0.47         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.20/0.47             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.20/0.47             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      ((((sk_A) != (sk_A)))
% 0.20/0.47         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.20/0.47             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.20/0.47             ~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.20/0.47             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.20/0.47       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.20/0.47       (((sk_A) = (k1_tarski @ sk_C))) | (((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['3', '5', '7', '37'])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['1', '38'])).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      ((((sk_A) = (k1_tarski @ sk_C))) <= ((((sk_A) = (k1_tarski @ sk_C))))),
% 0.20/0.47      inference('split', [status(esa)], ['8'])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.20/0.47       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      ((((sk_A) = (k2_tarski @ sk_B @ sk_C)))
% 0.20/0.47         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.20/0.47      inference('split', [status(esa)], ['8'])).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.20/0.47         ((r1_tarski @ X6 @ (k2_tarski @ X4 @ X7))
% 0.20/0.47          | ((X6) != (k2_tarski @ X4 @ X7)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      (![X4 : $i, X7 : $i]:
% 0.20/0.47         (r1_tarski @ (k2_tarski @ X4 @ X7) @ (k2_tarski @ X4 @ X7))),
% 0.20/0.47      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.47  thf('45', plain,
% 0.20/0.47      (((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))
% 0.20/0.47         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.20/0.47      inference('sup+', [status(thm)], ['42', '44'])).
% 0.20/0.47  thf('46', plain,
% 0.20/0.47      ((((sk_A) = (k2_tarski @ sk_B @ sk_C)))
% 0.20/0.47         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.20/0.47      inference('split', [status(esa)], ['8'])).
% 0.20/0.47  thf('47', plain,
% 0.20/0.47      (((r1_tarski @ sk_A @ sk_A)) <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.20/0.47      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.47  thf('48', plain,
% 0.20/0.47      (![X0 : $i, X2 : $i]:
% 0.20/0.47         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.47  thf('49', plain,
% 0.20/0.47      ((((k4_xboole_0 @ sk_A @ sk_A) = (k1_xboole_0)))
% 0.20/0.47         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.47  thf('50', plain,
% 0.20/0.47      ((((sk_A) = (k2_tarski @ sk_B @ sk_C)))
% 0.20/0.47         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.20/0.47      inference('split', [status(esa)], ['8'])).
% 0.20/0.47  thf('51', plain,
% 0.20/0.47      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('52', plain,
% 0.20/0.47      ((((k4_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.20/0.47             (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.47  thf('53', plain,
% 0.20/0.47      (~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['3', '5', '7', '37'])).
% 0.20/0.47  thf('54', plain,
% 0.20/0.47      ((((k4_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0)))
% 0.20/0.47         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['52', '53'])).
% 0.20/0.47  thf('55', plain, (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['49', '54'])).
% 0.20/0.47  thf('56', plain,
% 0.20/0.47      (~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.20/0.47       (((sk_A) = (k1_tarski @ sk_B))) | (((sk_A) = (k1_tarski @ sk_C))) | 
% 0.20/0.47       (((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.47  thf('57', plain,
% 0.20/0.47      ((((sk_A) = (k1_tarski @ sk_B))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.20/0.47      inference('split', [status(esa)], ['8'])).
% 0.20/0.47  thf('58', plain,
% 0.20/0.47      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.20/0.47         ((r1_tarski @ X6 @ (k2_tarski @ X4 @ X7)) | ((X6) != (k1_tarski @ X4)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.20/0.47  thf('59', plain,
% 0.20/0.47      (![X4 : $i, X7 : $i]:
% 0.20/0.47         (r1_tarski @ (k1_tarski @ X4) @ (k2_tarski @ X4 @ X7))),
% 0.20/0.47      inference('simplify', [status(thm)], ['58'])).
% 0.20/0.47  thf('60', plain,
% 0.20/0.47      (![X0 : $i, X2 : $i]:
% 0.20/0.47         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.47  thf('61', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.20/0.47           = (k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.47  thf('62', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ X0)) = (k1_xboole_0)))
% 0.20/0.47         <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.20/0.47      inference('sup+', [status(thm)], ['57', '61'])).
% 0.20/0.47  thf('63', plain,
% 0.20/0.47      (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['1', '38'])).
% 0.20/0.47  thf('64', plain,
% 0.20/0.47      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.47  thf('65', plain, (~ (((sk_A) = (k1_tarski @ sk_B)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['64'])).
% 0.20/0.47  thf('66', plain,
% 0.20/0.47      ((((sk_A) = (k1_tarski @ sk_C))) | (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.20/0.47       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.20/0.47       (((sk_A) = (k2_tarski @ sk_B @ sk_C))) | (((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('split', [status(esa)], ['8'])).
% 0.20/0.47  thf('67', plain, ((((sk_A) = (k1_tarski @ sk_C)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)],
% 0.20/0.47                ['19', '41', '55', '3', '5', '7', '56', '65', '66'])).
% 0.20/0.47  thf('68', plain, (((sk_A) = (k1_tarski @ sk_C))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['40', '67'])).
% 0.20/0.47  thf('69', plain,
% 0.20/0.47      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.20/0.47         ((r1_tarski @ X6 @ (k2_tarski @ X4 @ X7)) | ((X6) != (k1_tarski @ X7)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.20/0.47  thf('70', plain,
% 0.20/0.47      (![X4 : $i, X7 : $i]:
% 0.20/0.47         (r1_tarski @ (k1_tarski @ X7) @ (k2_tarski @ X4 @ X7))),
% 0.20/0.47      inference('simplify', [status(thm)], ['69'])).
% 0.20/0.47  thf('71', plain,
% 0.20/0.47      (![X0 : $i, X2 : $i]:
% 0.20/0.47         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.47  thf('72', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.20/0.47           = (k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.47  thf('73', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k4_xboole_0 @ sk_A @ (k2_tarski @ X0 @ sk_C)) = (k1_xboole_0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['68', '72'])).
% 0.20/0.47  thf('74', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['39', '73'])).
% 0.20/0.47  thf('75', plain, ($false), inference('simplify', [status(thm)], ['74'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

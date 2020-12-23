%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MrDFGWLBX9

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:42 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 250 expanded)
%              Number of leaves         :   16 (  62 expanded)
%              Depth                    :   23
%              Number of atoms          :  896 (3710 expanded)
%              Number of equality atoms :  169 ( 768 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
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
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X13
        = ( k2_tarski @ X11 @ X12 ) )
      | ( X13
        = ( k1_tarski @ X12 ) )
      | ( X13
        = ( k1_tarski @ X11 ) )
      | ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ ( k2_tarski @ X11 @ X12 ) ) ) ),
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
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
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
    ! [X10: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X10 )
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
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('25',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
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
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['14','28'])).

thf('30',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('31',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
   <= ( sk_A
     != ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('34',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('37',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','5','7','38'])).

thf('40',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','39'])).

thf('41',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_C ) )
   <= ( sk_A
      = ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['8'])).

thf('42',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('43',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['8'])).

thf('54',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
     != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf(t22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = k1_xboole_0 ) )).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X15 ) @ ( k2_tarski @ X15 @ X16 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t22_zfmisc_1])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ X0 ) )
        = k1_xboole_0 )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
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

thf('65',plain,
    ( sk_A
    = ( k1_tarski @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['16','42','57','3','5','7','38','63','64'])).

thf('66',plain,
    ( sk_A
    = ( k1_tarski @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['41','65'])).

thf('67',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ ( k2_tarski @ X11 @ X14 ) )
      | ( X13
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('68',plain,(
    ! [X11: $i,X14: $i] :
      ( r1_tarski @ ( k1_tarski @ X14 ) @ ( k2_tarski @ X11 @ X14 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_tarski @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ X0 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['40','71'])).

thf('73',plain,(
    $false ),
    inference(simplify,[status(thm)],['72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MrDFGWLBX9
% 0.13/0.32  % Computer   : n009.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 12:13:41 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running portfolio for 600 s
% 0.13/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.32  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 173 iterations in 0.047s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.48  thf(t75_zfmisc_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.48       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.19/0.48            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.48        ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.48          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.19/0.48               ( ( A ) != ( k1_tarski @ C ) ) & 
% 0.19/0.48               ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t75_zfmisc_1])).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      ((((sk_A) != (k1_xboole_0))
% 0.19/0.48        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.19/0.48         <= (~
% 0.19/0.48             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      ((((sk_A) != (k1_tarski @ sk_B))
% 0.19/0.48        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.19/0.48       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.19/0.48      inference('split', [status(esa)], ['2'])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      ((((sk_A) != (k1_tarski @ sk_C))
% 0.19/0.48        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.19/0.48       ~ (((sk_A) = (k1_tarski @ sk_C)))),
% 0.19/0.48      inference('split', [status(esa)], ['4'])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      ((((sk_A) != (k2_tarski @ sk_B @ sk_C))
% 0.19/0.48        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) | 
% 0.19/0.48       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.19/0.48      inference('split', [status(esa)], ['6'])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      ((((sk_A) = (k2_tarski @ sk_B @ sk_C))
% 0.19/0.48        | ((sk_A) = (k1_tarski @ sk_C))
% 0.19/0.48        | ((sk_A) = (k1_tarski @ sk_B))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))
% 0.19/0.48         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['8'])).
% 0.19/0.48  thf(l32_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.48         | (r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))))
% 0.19/0.48         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))
% 0.19/0.48         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.48  thf(l45_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.19/0.48       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.19/0.48            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.48         (((X13) = (k2_tarski @ X11 @ X12))
% 0.19/0.48          | ((X13) = (k1_tarski @ X12))
% 0.19/0.48          | ((X13) = (k1_tarski @ X11))
% 0.19/0.48          | ((X13) = (k1_xboole_0))
% 0.19/0.48          | ~ (r1_tarski @ X13 @ (k2_tarski @ X11 @ X12)))),
% 0.19/0.48      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (((((sk_A) = (k1_xboole_0))
% 0.19/0.48         | ((sk_A) = (k1_tarski @ sk_B))
% 0.19/0.48         | ((sk_A) = (k1_tarski @ sk_C))
% 0.19/0.48         | ((sk_A) = (k2_tarski @ sk_B @ sk_C))))
% 0.19/0.48         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.19/0.49       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('split', [status(esa)], ['8'])).
% 0.19/0.49  thf(t4_boole, axiom,
% 0.19/0.49    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X10 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [t4_boole])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      ((![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0)))
% 0.19/0.49         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('sup+', [status(thm)], ['17', '18'])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('split', [status(esa)], ['8'])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      ((![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (sk_A)))
% 0.19/0.49         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.19/0.49         <= (~
% 0.19/0.49             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      ((((sk_A) != (k1_xboole_0)))
% 0.19/0.49         <= (~
% 0.19/0.49             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.19/0.49             (((sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('split', [status(esa)], ['8'])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      ((((sk_A) != (sk_A)))
% 0.19/0.49         <= (~
% 0.19/0.49             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.19/0.49             (((sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('demod', [status(thm)], ['23', '24'])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.19/0.49       ~ (((sk_A) = (k1_xboole_0)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['25'])).
% 0.19/0.49  thf('27', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['16', '26'])).
% 0.19/0.49  thf('28', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['15', '27'])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (((((sk_A) = (k1_tarski @ sk_B))
% 0.19/0.49         | ((sk_A) = (k1_tarski @ sk_C))
% 0.19/0.49         | ((sk_A) = (k2_tarski @ sk_B @ sk_C))))
% 0.19/0.49         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['14', '28'])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      ((((sk_A) != (k2_tarski @ sk_B @ sk_C)))
% 0.19/0.49         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.19/0.49      inference('split', [status(esa)], ['6'])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (((((sk_A) != (sk_A))
% 0.19/0.49         | ((sk_A) = (k1_tarski @ sk_C))
% 0.19/0.49         | ((sk_A) = (k1_tarski @ sk_B))))
% 0.19/0.49         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.19/0.49             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.49  thf('32', plain,
% 0.19/0.49      (((((sk_A) = (k1_tarski @ sk_B)) | ((sk_A) = (k1_tarski @ sk_C))))
% 0.19/0.49         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.19/0.49             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.19/0.49      inference('simplify', [status(thm)], ['31'])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      ((((sk_A) != (k1_tarski @ sk_C))) <= (~ (((sk_A) = (k1_tarski @ sk_C))))),
% 0.19/0.49      inference('split', [status(esa)], ['4'])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      (((((sk_A) != (sk_A)) | ((sk_A) = (k1_tarski @ sk_B))))
% 0.19/0.49         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.19/0.49             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.19/0.49             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      ((((sk_A) = (k1_tarski @ sk_B)))
% 0.19/0.49         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.19/0.49             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.19/0.49             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.19/0.49      inference('simplify', [status(thm)], ['34'])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.19/0.49      inference('split', [status(esa)], ['2'])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      ((((sk_A) != (sk_A)))
% 0.19/0.49         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.19/0.49             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.19/0.49             ~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.19/0.49             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      (~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.19/0.49       (((sk_A) = (k1_tarski @ sk_B))) | (((sk_A) = (k1_tarski @ sk_C))) | 
% 0.19/0.49       (((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['37'])).
% 0.19/0.49  thf('39', plain,
% 0.19/0.49      (~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['3', '5', '7', '38'])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['1', '39'])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      ((((sk_A) = (k1_tarski @ sk_C))) <= ((((sk_A) = (k1_tarski @ sk_C))))),
% 0.19/0.49      inference('split', [status(esa)], ['8'])).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.19/0.49       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['25'])).
% 0.19/0.49  thf('43', plain,
% 0.19/0.49      (![X10 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [t4_boole])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.49  thf('46', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.49      inference('simplify', [status(thm)], ['45'])).
% 0.19/0.49  thf(t12_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.19/0.49  thf('47', plain,
% 0.19/0.49      (![X3 : $i, X4 : $i]:
% 0.19/0.49         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.19/0.49  thf('48', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.49  thf(t40_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.19/0.49  thf('49', plain,
% 0.19/0.49      (![X8 : $i, X9 : $i]:
% 0.19/0.49         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 0.19/0.49           = (k4_xboole_0 @ X8 @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.19/0.49  thf('50', plain,
% 0.19/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['48', '49'])).
% 0.19/0.49  thf('51', plain,
% 0.19/0.49      (![X10 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [t4_boole])).
% 0.19/0.49  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['50', '51'])).
% 0.19/0.49  thf('53', plain,
% 0.19/0.49      ((((sk_A) = (k2_tarski @ sk_B @ sk_C)))
% 0.19/0.49         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.19/0.49      inference('split', [status(esa)], ['8'])).
% 0.19/0.49  thf('54', plain,
% 0.19/0.49      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.19/0.49         <= (~
% 0.19/0.49             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('55', plain,
% 0.19/0.49      ((((k4_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0)))
% 0.19/0.49         <= (~
% 0.19/0.49             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.19/0.49             (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['53', '54'])).
% 0.19/0.49  thf('56', plain,
% 0.19/0.49      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.49         <= (~
% 0.19/0.49             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.19/0.49             (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['52', '55'])).
% 0.19/0.49  thf('57', plain,
% 0.19/0.49      (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) | 
% 0.19/0.49       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['56'])).
% 0.19/0.49  thf('58', plain,
% 0.19/0.49      ((((sk_A) = (k1_tarski @ sk_B))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.19/0.49      inference('split', [status(esa)], ['8'])).
% 0.19/0.49  thf(t22_zfmisc_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.19/0.49       ( k1_xboole_0 ) ))).
% 0.19/0.49  thf('59', plain,
% 0.19/0.49      (![X15 : $i, X16 : $i]:
% 0.19/0.49         ((k4_xboole_0 @ (k1_tarski @ X15) @ (k2_tarski @ X15 @ X16))
% 0.19/0.49           = (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [t22_zfmisc_1])).
% 0.19/0.49  thf('60', plain,
% 0.19/0.49      ((![X0 : $i]:
% 0.19/0.49          ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ X0)) = (k1_xboole_0)))
% 0.19/0.49         <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.19/0.49      inference('sup+', [status(thm)], ['58', '59'])).
% 0.19/0.49  thf('61', plain,
% 0.19/0.49      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.19/0.49         <= (~
% 0.19/0.49             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('62', plain,
% 0.19/0.49      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.49         <= (~
% 0.19/0.49             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.19/0.49             (((sk_A) = (k1_tarski @ sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['60', '61'])).
% 0.19/0.49  thf('63', plain,
% 0.19/0.49      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.19/0.49       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['62'])).
% 0.19/0.49  thf('64', plain,
% 0.19/0.49      ((((sk_A) = (k1_tarski @ sk_C))) | (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.19/0.49       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.19/0.49       (((sk_A) = (k2_tarski @ sk_B @ sk_C))) | (((sk_A) = (k1_xboole_0)))),
% 0.19/0.49      inference('split', [status(esa)], ['8'])).
% 0.19/0.49  thf('65', plain, ((((sk_A) = (k1_tarski @ sk_C)))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)],
% 0.19/0.49                ['16', '42', '57', '3', '5', '7', '38', '63', '64'])).
% 0.19/0.49  thf('66', plain, (((sk_A) = (k1_tarski @ sk_C))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['41', '65'])).
% 0.19/0.49  thf('67', plain,
% 0.19/0.49      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.19/0.49         ((r1_tarski @ X13 @ (k2_tarski @ X11 @ X14))
% 0.19/0.49          | ((X13) != (k1_tarski @ X14)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.19/0.49  thf('68', plain,
% 0.19/0.49      (![X11 : $i, X14 : $i]:
% 0.19/0.49         (r1_tarski @ (k1_tarski @ X14) @ (k2_tarski @ X11 @ X14))),
% 0.19/0.49      inference('simplify', [status(thm)], ['67'])).
% 0.19/0.49  thf('69', plain, (![X0 : $i]: (r1_tarski @ sk_A @ (k2_tarski @ X0 @ sk_C))),
% 0.19/0.49      inference('sup+', [status(thm)], ['66', '68'])).
% 0.19/0.49  thf('70', plain,
% 0.19/0.49      (![X0 : $i, X2 : $i]:
% 0.19/0.49         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.49  thf('71', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k4_xboole_0 @ sk_A @ (k2_tarski @ X0 @ sk_C)) = (k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['69', '70'])).
% 0.19/0.49  thf('72', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['40', '71'])).
% 0.19/0.49  thf('73', plain, ($false), inference('simplify', [status(thm)], ['72'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

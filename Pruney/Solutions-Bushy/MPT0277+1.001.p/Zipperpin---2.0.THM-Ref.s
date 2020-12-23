%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0277+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W7boSwrM2h

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:38 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 869 expanded)
%              Number of leaves         :   12 ( 193 expanded)
%              Depth                    :   24
%              Number of atoms          :  887 (13697 expanded)
%              Number of equality atoms :  164 (2798 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('8',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

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

thf('11',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ ( k2_tarski @ X0 @ X3 ) )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X3: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ X0 ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ X0 ) )
        = k1_xboole_0 )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
     != ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('25',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_tarski @ X0 @ X1 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('28',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('30',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('31',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','30'])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','31'])).

thf('33',plain,
    ( ( ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['28','32'])).

thf('34',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['21'])).

thf('35',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
   <= ( sk_A
     != ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['19'])).

thf('38',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['17'])).

thf('41',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['18','20','22','42'])).

thf('44',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['16','43'])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','44'])).

thf('46',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('48',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_C ) )
   <= ( sk_A
      = ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ ( k2_tarski @ X0 @ X3 ) )
      | ( X2
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i,X3: $i] :
      ( r1_tarski @ ( k1_tarski @ X3 ) @ ( k2_tarski @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ X0 @ sk_C ) )
        = k1_xboole_0 )
   <= ( sk_A
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup+',[status(thm)],['48','52'])).

thf('54',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['16','43'])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    sk_A
 != ( k1_tarski @ sk_C ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( sk_A
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['3','9','46','18','20','22','47','56','57'])).

thf('59',plain,
    ( sk_A
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','58'])).

thf('60',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ ( k2_tarski @ X0 @ X3 ) )
      | ( X2
       != ( k2_tarski @ X0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i,X3: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X3 ) @ ( k2_tarski @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['59','63'])).

thf('65',plain,
    ( sk_A
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','58'])).

thf('66',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('69',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
     != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['18','20','22','42'])).

thf('71',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
     != k1_xboole_0 )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['69','70'])).

thf('72',plain,
    ( sk_A
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['3','9','46','18','20','22','47','56','57'])).

thf('73',plain,(
    ( k4_xboole_0 @ sk_A @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['66','73'])).


%------------------------------------------------------------------------------

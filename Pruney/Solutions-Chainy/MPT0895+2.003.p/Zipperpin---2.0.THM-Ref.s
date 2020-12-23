%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HcKRjgKSVM

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:38 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 623 expanded)
%              Number of leaves         :   12 ( 141 expanded)
%              Depth                    :   24
%              Number of atoms          : 1023 (8808 expanded)
%              Number of equality atoms :  231 (2147 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t55_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ( D != k1_xboole_0 ) )
      <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
         != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t55_mcart_1])).

thf('0',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('5',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D )
        = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D )
        = sk_D )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( sk_D != k1_xboole_0 )
   <= ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
       != k1_xboole_0 )
      & ( sk_D = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( sk_D != sk_D )
   <= ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
       != k1_xboole_0 )
      & ( sk_D = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_D != k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( X7 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X7 @ X8 @ X10 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('18',plain,(
    ! [X8: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X8 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('22',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','22'])).

thf('24',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('28',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('29',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_D != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_D != k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,
    ( ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
       != k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('42',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( sk_D != k1_xboole_0 )
   <= ( sk_D != k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('45',plain,
    ( ( ( sk_D != sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('48',plain,
    ( ( ( sk_C != sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('51',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('54',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['28','30','32','34','55'])).

thf('57',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['27','56'])).

thf('58',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','57'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    sk_A != k1_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('63',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( X8 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X7 @ X8 @ X10 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('65',plain,(
    ! [X7: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X7 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0 )
        = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','69'])).

thf('71',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0 )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['27','56'])).

thf('74',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    sk_B != k1_xboole_0 ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('79',plain,(
    sk_C = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['15','61','28','30','32','34','62','77','78'])).

thf('80',plain,(
    sk_C = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','79'])).

thf('81',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['27','56'])).

thf('82',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( X10 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X7 @ X8 @ X10 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('84',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
        = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['82','88'])).

thf('90',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('91',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
        = sk_C )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    sk_C = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['15','61','28','30','32','34','62','77','78'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
      = sk_C ) ),
    inference(simpl_trail,[status(thm)],['91','92'])).

thf('94',plain,(
    sk_C != k1_xboole_0 ),
    inference(demod,[status(thm)],['81','93'])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['80','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HcKRjgKSVM
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:03:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.56  % Solved by: fo/fo7.sh
% 0.36/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.56  % done 493 iterations in 0.100s
% 0.36/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.56  % SZS output start Refutation
% 0.36/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.56  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.36/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.56  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(t55_mcart_1, conjecture,
% 0.36/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.56     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.36/0.56         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.36/0.56       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.36/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.56        ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.36/0.56            ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.36/0.56          ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t55_mcart_1])).
% 0.36/0.56  thf('0', plain,
% 0.36/0.56      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))
% 0.36/0.56        | ((sk_D) = (k1_xboole_0))
% 0.36/0.56        | ((sk_C) = (k1_xboole_0))
% 0.36/0.56        | ((sk_B) = (k1_xboole_0))
% 0.36/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('1', plain, ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('2', plain, ((((sk_D) = (k1_xboole_0))) <= ((((sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf(d4_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.56     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.36/0.56       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.36/0.56  thf('3', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.56         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.36/0.56           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.36/0.56      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.36/0.56  thf(t113_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.56  thf('4', plain,
% 0.36/0.56      (![X1 : $i, X2 : $i]:
% 0.36/0.56         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.56  thf('5', plain,
% 0.36/0.56      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.56      inference('simplify', [status(thm)], ['4'])).
% 0.36/0.56  thf('6', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['3', '5'])).
% 0.36/0.56  thf('7', plain,
% 0.36/0.56      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56          ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D) = (k1_xboole_0)))
% 0.36/0.56         <= ((((sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('sup+', [status(thm)], ['2', '6'])).
% 0.36/0.56  thf('8', plain, ((((sk_D) = (k1_xboole_0))) <= ((((sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('9', plain,
% 0.36/0.56      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56          ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D) = (sk_D)))
% 0.36/0.56         <= ((((sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.56  thf('10', plain,
% 0.36/0.56      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))
% 0.36/0.56        | ((sk_A) != (k1_xboole_0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('11', plain,
% 0.36/0.56      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0)))
% 0.36/0.56         <= (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['10'])).
% 0.36/0.56  thf('12', plain,
% 0.36/0.56      ((((sk_D) != (k1_xboole_0)))
% 0.36/0.56         <= (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) & 
% 0.36/0.56             (((sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['9', '11'])).
% 0.36/0.56  thf('13', plain,
% 0.36/0.56      ((((sk_D) = (k1_xboole_0))) <= ((((sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('14', plain,
% 0.36/0.56      ((((sk_D) != (sk_D)))
% 0.36/0.56         <= (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) & 
% 0.36/0.56             (((sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.56  thf('15', plain,
% 0.36/0.56      (~ (((sk_D) = (k1_xboole_0))) | 
% 0.36/0.56       (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['14'])).
% 0.36/0.56  thf('16', plain,
% 0.36/0.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf(t35_mcart_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.36/0.56         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.36/0.56       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.36/0.56  thf('17', plain,
% 0.36/0.56      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.36/0.56         (((X7) != (k1_xboole_0))
% 0.36/0.56          | ((k3_zfmisc_1 @ X7 @ X8 @ X10) = (k1_xboole_0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.36/0.56  thf('18', plain,
% 0.36/0.56      (![X8 : $i, X10 : $i]:
% 0.36/0.56         ((k3_zfmisc_1 @ k1_xboole_0 @ X8 @ X10) = (k1_xboole_0))),
% 0.36/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.36/0.56  thf('19', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.56         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.36/0.56           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.36/0.56      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.36/0.56  thf('20', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0)
% 0.36/0.56           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['18', '19'])).
% 0.36/0.56  thf('21', plain,
% 0.36/0.56      (![X1 : $i, X2 : $i]:
% 0.36/0.56         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.56  thf('22', plain,
% 0.36/0.56      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.36/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.36/0.56  thf('23', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0) = (k1_xboole_0))),
% 0.36/0.56      inference('demod', [status(thm)], ['20', '22'])).
% 0.36/0.56  thf('24', plain,
% 0.36/0.56      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56          ((k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0) = (k1_xboole_0)))
% 0.36/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.56      inference('sup+', [status(thm)], ['16', '23'])).
% 0.36/0.56  thf('25', plain,
% 0.36/0.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('26', plain,
% 0.36/0.56      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56          ((k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0) = (sk_A)))
% 0.36/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.56      inference('demod', [status(thm)], ['24', '25'])).
% 0.36/0.56  thf('27', plain,
% 0.36/0.56      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0)))
% 0.36/0.56         <= (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['10'])).
% 0.36/0.56  thf('28', plain,
% 0.36/0.56      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.36/0.56       ~ (((sk_A) = (k1_xboole_0)))),
% 0.36/0.56      inference('split', [status(esa)], ['10'])).
% 0.36/0.56  thf('29', plain,
% 0.36/0.56      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))
% 0.36/0.56        | ((sk_B) != (k1_xboole_0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('30', plain,
% 0.36/0.56      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.36/0.56       ~ (((sk_B) = (k1_xboole_0)))),
% 0.36/0.56      inference('split', [status(esa)], ['29'])).
% 0.36/0.56  thf('31', plain,
% 0.36/0.56      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))
% 0.36/0.56        | ((sk_C) != (k1_xboole_0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('32', plain,
% 0.36/0.56      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.36/0.56       ~ (((sk_C) = (k1_xboole_0)))),
% 0.36/0.56      inference('split', [status(esa)], ['31'])).
% 0.36/0.56  thf('33', plain,
% 0.36/0.56      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))
% 0.36/0.56        | ((sk_D) != (k1_xboole_0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('34', plain,
% 0.36/0.56      (~ (((sk_D) = (k1_xboole_0))) | 
% 0.36/0.56       ~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0)))),
% 0.36/0.56      inference('split', [status(esa)], ['33'])).
% 0.36/0.56  thf('35', plain,
% 0.36/0.56      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0)))
% 0.36/0.56         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('36', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.56         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.36/0.56           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.36/0.56      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.36/0.56  thf('37', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (((X0) = (k1_xboole_0))
% 0.36/0.56          | ((X1) = (k1_xboole_0))
% 0.36/0.56          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.56  thf('38', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.56         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.36/0.56          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0))
% 0.36/0.56          | ((X0) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.56  thf('39', plain,
% 0.36/0.56      (((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.56         | ((sk_D) = (k1_xboole_0))
% 0.36/0.56         | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))))
% 0.36/0.56         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['35', '38'])).
% 0.36/0.56  thf('40', plain,
% 0.36/0.56      (((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 0.36/0.56         | ((sk_D) = (k1_xboole_0))))
% 0.36/0.56         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('simplify', [status(thm)], ['39'])).
% 0.36/0.56  thf('41', plain,
% 0.36/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.56         (((k3_zfmisc_1 @ X7 @ X8 @ X9) != (k1_xboole_0))
% 0.36/0.56          | ((X9) = (k1_xboole_0))
% 0.36/0.56          | ((X8) = (k1_xboole_0))
% 0.36/0.56          | ((X7) = (k1_xboole_0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.36/0.56  thf('42', plain,
% 0.36/0.56      (((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.56         | ((sk_D) = (k1_xboole_0))
% 0.36/0.56         | ((sk_A) = (k1_xboole_0))
% 0.36/0.56         | ((sk_B) = (k1_xboole_0))
% 0.36/0.56         | ((sk_C) = (k1_xboole_0))))
% 0.36/0.56         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.56  thf('43', plain,
% 0.36/0.56      (((((sk_C) = (k1_xboole_0))
% 0.36/0.56         | ((sk_B) = (k1_xboole_0))
% 0.36/0.56         | ((sk_A) = (k1_xboole_0))
% 0.36/0.56         | ((sk_D) = (k1_xboole_0))))
% 0.36/0.56         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('simplify', [status(thm)], ['42'])).
% 0.36/0.56  thf('44', plain,
% 0.36/0.56      ((((sk_D) != (k1_xboole_0))) <= (~ (((sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['33'])).
% 0.36/0.56  thf('45', plain,
% 0.36/0.56      (((((sk_D) != (sk_D))
% 0.36/0.56         | ((sk_A) = (k1_xboole_0))
% 0.36/0.56         | ((sk_B) = (k1_xboole_0))
% 0.36/0.56         | ((sk_C) = (k1_xboole_0))))
% 0.36/0.56         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.36/0.56             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.56  thf('46', plain,
% 0.36/0.56      (((((sk_C) = (k1_xboole_0))
% 0.36/0.56         | ((sk_B) = (k1_xboole_0))
% 0.36/0.56         | ((sk_A) = (k1_xboole_0))))
% 0.36/0.56         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.36/0.56             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('simplify', [status(thm)], ['45'])).
% 0.36/0.56  thf('47', plain,
% 0.36/0.56      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['31'])).
% 0.36/0.56  thf('48', plain,
% 0.36/0.56      (((((sk_C) != (sk_C))
% 0.36/0.56         | ((sk_A) = (k1_xboole_0))
% 0.36/0.56         | ((sk_B) = (k1_xboole_0))))
% 0.36/0.56         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.36/0.56             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.36/0.56             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.36/0.56  thf('49', plain,
% 0.36/0.56      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.36/0.56         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.36/0.56             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.36/0.56             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('simplify', [status(thm)], ['48'])).
% 0.36/0.56  thf('50', plain,
% 0.36/0.56      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['29'])).
% 0.36/0.56  thf('51', plain,
% 0.36/0.56      (((((sk_B) != (sk_B)) | ((sk_A) = (k1_xboole_0))))
% 0.36/0.56         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.36/0.56             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.36/0.56             ~ (((sk_B) = (k1_xboole_0))) & 
% 0.36/0.56             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.56  thf('52', plain,
% 0.36/0.56      ((((sk_A) = (k1_xboole_0)))
% 0.36/0.56         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.36/0.56             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.36/0.56             ~ (((sk_B) = (k1_xboole_0))) & 
% 0.36/0.56             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('simplify', [status(thm)], ['51'])).
% 0.36/0.56  thf('53', plain,
% 0.36/0.56      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['10'])).
% 0.36/0.56  thf('54', plain,
% 0.36/0.56      ((((sk_A) != (sk_A)))
% 0.36/0.56         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.36/0.56             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.36/0.56             ~ (((sk_B) = (k1_xboole_0))) & 
% 0.36/0.56             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.36/0.56             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.36/0.56  thf('55', plain,
% 0.36/0.56      ((((sk_A) = (k1_xboole_0))) | 
% 0.36/0.56       ~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.36/0.56       (((sk_B) = (k1_xboole_0))) | (((sk_C) = (k1_xboole_0))) | 
% 0.36/0.56       (((sk_D) = (k1_xboole_0)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['54'])).
% 0.36/0.56  thf('56', plain,
% 0.36/0.56      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0)))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)],
% 0.36/0.56                ['28', '30', '32', '34', '55'])).
% 0.36/0.56  thf('57', plain,
% 0.36/0.56      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['27', '56'])).
% 0.36/0.56  thf('58', plain,
% 0.36/0.56      ((((sk_A) != (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['26', '57'])).
% 0.36/0.56  thf('59', plain,
% 0.36/0.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('60', plain, ((((sk_A) != (sk_A))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.56      inference('demod', [status(thm)], ['58', '59'])).
% 0.36/0.56  thf('61', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['60'])).
% 0.36/0.56  thf('62', plain,
% 0.36/0.56      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.36/0.56       (((sk_A) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0))) | 
% 0.36/0.56       (((sk_C) = (k1_xboole_0))) | (((sk_D) = (k1_xboole_0)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['54'])).
% 0.36/0.56  thf('63', plain,
% 0.36/0.56      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('64', plain,
% 0.36/0.56      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.36/0.56         (((X8) != (k1_xboole_0))
% 0.36/0.56          | ((k3_zfmisc_1 @ X7 @ X8 @ X10) = (k1_xboole_0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.36/0.56  thf('65', plain,
% 0.36/0.56      (![X7 : $i, X10 : $i]:
% 0.36/0.56         ((k3_zfmisc_1 @ X7 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.36/0.56      inference('simplify', [status(thm)], ['64'])).
% 0.36/0.56  thf('66', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.56         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.36/0.56           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.36/0.56      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.36/0.56  thf('67', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0)
% 0.36/0.56           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['65', '66'])).
% 0.36/0.56  thf('68', plain,
% 0.36/0.56      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.36/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.36/0.56  thf('69', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.36/0.56      inference('demod', [status(thm)], ['67', '68'])).
% 0.36/0.56  thf('70', plain,
% 0.36/0.56      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56          ((k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0) = (k1_xboole_0)))
% 0.36/0.56         <= ((((sk_B) = (k1_xboole_0))))),
% 0.36/0.56      inference('sup+', [status(thm)], ['63', '69'])).
% 0.36/0.56  thf('71', plain,
% 0.36/0.56      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('72', plain,
% 0.36/0.56      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56          ((k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0) = (sk_B)))
% 0.36/0.56         <= ((((sk_B) = (k1_xboole_0))))),
% 0.36/0.56      inference('demod', [status(thm)], ['70', '71'])).
% 0.36/0.56  thf('73', plain,
% 0.36/0.56      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['27', '56'])).
% 0.36/0.56  thf('74', plain,
% 0.36/0.56      ((((sk_B) != (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['72', '73'])).
% 0.36/0.56  thf('75', plain,
% 0.36/0.56      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('76', plain, ((((sk_B) != (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.36/0.56      inference('demod', [status(thm)], ['74', '75'])).
% 0.36/0.56  thf('77', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['76'])).
% 0.36/0.56  thf('78', plain,
% 0.36/0.56      ((((sk_C) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0))) | 
% 0.36/0.56       (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.36/0.56       (((sk_A) = (k1_xboole_0))) | (((sk_D) = (k1_xboole_0)))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('79', plain, ((((sk_C) = (k1_xboole_0)))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)],
% 0.36/0.56                ['15', '61', '28', '30', '32', '34', '62', '77', '78'])).
% 0.36/0.56  thf('80', plain, (((sk_C) = (k1_xboole_0))),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['1', '79'])).
% 0.36/0.56  thf('81', plain,
% 0.36/0.56      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['27', '56'])).
% 0.36/0.56  thf('82', plain,
% 0.36/0.56      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('83', plain,
% 0.36/0.56      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.36/0.56         (((X10) != (k1_xboole_0))
% 0.36/0.56          | ((k3_zfmisc_1 @ X7 @ X8 @ X10) = (k1_xboole_0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.36/0.56  thf('84', plain,
% 0.36/0.56      (![X7 : $i, X8 : $i]:
% 0.36/0.56         ((k3_zfmisc_1 @ X7 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.56      inference('simplify', [status(thm)], ['83'])).
% 0.36/0.56  thf('85', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.56         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.36/0.56           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.36/0.56      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.36/0.56  thf('86', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0)
% 0.36/0.56           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['84', '85'])).
% 0.36/0.56  thf('87', plain,
% 0.36/0.56      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.36/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.36/0.56  thf('88', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.56      inference('demod', [status(thm)], ['86', '87'])).
% 0.36/0.56  thf('89', plain,
% 0.36/0.56      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56          ((k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0) = (k1_xboole_0)))
% 0.36/0.56         <= ((((sk_C) = (k1_xboole_0))))),
% 0.36/0.56      inference('sup+', [status(thm)], ['82', '88'])).
% 0.36/0.56  thf('90', plain,
% 0.36/0.56      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('91', plain,
% 0.36/0.56      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56          ((k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0) = (sk_C)))
% 0.36/0.56         <= ((((sk_C) = (k1_xboole_0))))),
% 0.36/0.56      inference('demod', [status(thm)], ['89', '90'])).
% 0.36/0.56  thf('92', plain, ((((sk_C) = (k1_xboole_0)))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)],
% 0.36/0.56                ['15', '61', '28', '30', '32', '34', '62', '77', '78'])).
% 0.36/0.56  thf('93', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0) = (sk_C))),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['91', '92'])).
% 0.36/0.56  thf('94', plain, (((sk_C) != (k1_xboole_0))),
% 0.36/0.56      inference('demod', [status(thm)], ['81', '93'])).
% 0.36/0.56  thf('95', plain, ($false),
% 0.36/0.56      inference('simplify_reflect-', [status(thm)], ['80', '94'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.36/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

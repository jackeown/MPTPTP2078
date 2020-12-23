%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0895+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qsY4w3NlEQ

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:40 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 624 expanded)
%              Number of leaves         :   12 ( 141 expanded)
%              Depth                    :   25
%              Number of atoms          : 1030 (8815 expanded)
%              Number of equality atoms :  232 (2148 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
     != k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_D != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_D != k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X0 @ X1 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
       != k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('17',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( sk_D != k1_xboole_0 )
   <= ( sk_D != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('20',plain,
    ( ( ( sk_D != sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('23',plain,
    ( ( ( sk_C != sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('26',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','4','6','8','30'])).

thf('32',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('33',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('34',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('36',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X0 @ X1 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D )
        = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','38'])).

thf('40',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('41',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D )
        = sk_D )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( sk_D != k1_xboole_0 )
   <= ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
       != k1_xboole_0 )
      & ( sk_D = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('45',plain,
    ( ( sk_D != sk_D )
   <= ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
       != k1_xboole_0 )
      & ( sk_D = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_D != k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('48',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( X7 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X7 @ X8 @ X10 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('49',plain,(
    ! [X8: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X8 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X0 @ X1 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('53',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','53'])).

thf('55',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','54'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('57',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('59',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('61',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    sk_A != k1_xboole_0 ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('64',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('65',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( X8 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X7 @ X8 @ X10 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('66',plain,(
    ! [X7: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X7 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X0 @ X1 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0 )
        = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','70'])).

thf('72',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('73',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0 )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('75',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('77',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    sk_B != k1_xboole_0 ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('80',plain,(
    sk_C = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['46','62','2','4','6','8','63','78','79'])).

thf('81',plain,(
    sk_C = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['33','80'])).

thf('82',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != sk_C ),
    inference(demod,[status(thm)],['32','81'])).

thf('83',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('84',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( X10 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X7 @ X8 @ X10 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('85',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X0 @ X1 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
        = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','89'])).

thf('91',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('92',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
        = sk_C )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    sk_C = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['46','62','2','4','6','8','63','78','79'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
      = sk_C ) ),
    inference(simpl_trail,[status(thm)],['92','93'])).

thf('95',plain,(
    sk_C != sk_C ),
    inference(demod,[status(thm)],['82','94'])).

thf('96',plain,(
    $false ),
    inference(simplify,[status(thm)],['95'])).


%------------------------------------------------------------------------------

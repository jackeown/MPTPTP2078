%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QoWDGRqzKv

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:38 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 784 expanded)
%              Number of leaves         :   12 ( 191 expanded)
%              Depth                    :   29
%              Number of atoms          : 1220 (10614 expanded)
%              Number of equality atoms :  258 (2431 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,
    ( ( ( sk_D = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('25',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('28',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( sk_D != k1_xboole_0 )
   <= ( sk_D != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('31',plain,
    ( ( ( sk_D != sk_D )
      | ( sk_C = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('34',plain,
    ( ( ( sk_C != sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('37',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','4','6','8','41'])).

thf('43',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','42'])).

thf('44',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('47',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('48',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('49',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','49'])).

thf('51',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D )
        = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','50'])).

thf('52',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('53',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D )
        = sk_D )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ( sk_D != k1_xboole_0 )
   <= ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
       != k1_xboole_0 )
      & ( sk_D = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('57',plain,
    ( ( sk_D != sk_D )
   <= ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
       != k1_xboole_0 )
      & ( sk_D = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_D != k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('60',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('61',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('66',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','66'])).

thf('68',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
        = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','67'])).

thf('69',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('70',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
        = sk_C )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','42'])).

thf('72',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('74',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    sk_C != k1_xboole_0 ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('77',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('78',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0 )
        = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','85'])).

thf('87',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('88',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0 )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','42'])).

thf('90',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('92',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    sk_B != k1_xboole_0 ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('95',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['58','75','2','4','6','8','41','93','94'])).

thf('96',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['45','95'])).

thf('97',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != sk_A ),
    inference(demod,[status(thm)],['43','96'])).

thf('98',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('99',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('100',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','107'])).

thf('109',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('110',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['58','75','2','4','6','8','41','93','94'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0 )
      = sk_A ) ),
    inference(simpl_trail,[status(thm)],['110','111'])).

thf('113',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['97','112'])).

thf('114',plain,(
    $false ),
    inference(simplify,[status(thm)],['113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QoWDGRqzKv
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 685 iterations in 0.137s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.40/0.59  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.40/0.59  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.40/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.59  thf(t55_mcart_1, conjecture,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.40/0.59         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.40/0.59       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59        ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.40/0.59            ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.40/0.59          ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t55_mcart_1])).
% 0.40/0.59  thf('0', plain,
% 0.40/0.59      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))
% 0.40/0.59        | ((sk_A) != (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('1', plain,
% 0.40/0.59      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0)))
% 0.40/0.59         <= (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['0'])).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.40/0.59       ~ (((sk_A) = (k1_xboole_0)))),
% 0.40/0.59      inference('split', [status(esa)], ['0'])).
% 0.40/0.59  thf('3', plain,
% 0.40/0.59      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))
% 0.40/0.59        | ((sk_B) != (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.40/0.59       ~ (((sk_B) = (k1_xboole_0)))),
% 0.40/0.59      inference('split', [status(esa)], ['3'])).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))
% 0.40/0.59        | ((sk_C) != (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('6', plain,
% 0.40/0.59      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.40/0.59       ~ (((sk_C) = (k1_xboole_0)))),
% 0.40/0.59      inference('split', [status(esa)], ['5'])).
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))
% 0.40/0.59        | ((sk_D) != (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      (~ (((sk_D) = (k1_xboole_0))) | 
% 0.40/0.59       ~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0)))),
% 0.40/0.59      inference('split', [status(esa)], ['7'])).
% 0.40/0.59  thf('9', plain,
% 0.40/0.59      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))
% 0.40/0.59        | ((sk_D) = (k1_xboole_0))
% 0.40/0.59        | ((sk_C) = (k1_xboole_0))
% 0.40/0.59        | ((sk_B) = (k1_xboole_0))
% 0.40/0.59        | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('10', plain,
% 0.40/0.59      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0)))
% 0.40/0.59         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['9'])).
% 0.40/0.59  thf(d3_zfmisc_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.40/0.59       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.59         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.40/0.59           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.59         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.40/0.59           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.59         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.40/0.59           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.40/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.40/0.59  thf('14', plain,
% 0.40/0.59      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.59         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.40/0.59           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.40/0.59  thf(t113_zfmisc_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.40/0.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.59  thf('15', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (((X0) = (k1_xboole_0))
% 0.40/0.59          | ((X1) = (k1_xboole_0))
% 0.40/0.59          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.40/0.59          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.40/0.59          | ((X0) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.59         (((k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 0.40/0.59          | ((X0) = (k1_xboole_0))
% 0.40/0.59          | ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['13', '16'])).
% 0.40/0.59  thf('18', plain,
% 0.40/0.59      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.59         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.40/0.59           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.59         (((k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 0.40/0.59          | ((X0) = (k1_xboole_0))
% 0.40/0.59          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['17', '18'])).
% 0.40/0.59  thf(d4_zfmisc_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.40/0.59       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.40/0.59         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.40/0.59           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.40/0.59      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.59         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.40/0.59          | ((X0) = (k1_xboole_0))
% 0.40/0.59          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['19', '20'])).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      (((((k1_xboole_0) != (k1_xboole_0))
% 0.40/0.59         | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 0.40/0.59         | ((sk_D) = (k1_xboole_0))))
% 0.40/0.59         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['10', '21'])).
% 0.40/0.59  thf('23', plain,
% 0.40/0.59      (((((sk_D) = (k1_xboole_0))
% 0.40/0.59         | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))))
% 0.40/0.59         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('simplify', [status(thm)], ['22'])).
% 0.40/0.59  thf('24', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.40/0.59          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.40/0.59          | ((X0) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.59  thf('25', plain,
% 0.40/0.59      (((((k1_xboole_0) != (k1_xboole_0))
% 0.40/0.59         | ((sk_D) = (k1_xboole_0))
% 0.40/0.59         | ((sk_C) = (k1_xboole_0))
% 0.40/0.59         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.40/0.59         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      (((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.40/0.59         | ((sk_C) = (k1_xboole_0))
% 0.40/0.59         | ((sk_D) = (k1_xboole_0))))
% 0.40/0.59         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('simplify', [status(thm)], ['25'])).
% 0.40/0.59  thf('27', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (((X0) = (k1_xboole_0))
% 0.40/0.59          | ((X1) = (k1_xboole_0))
% 0.40/0.59          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      (((((k1_xboole_0) != (k1_xboole_0))
% 0.40/0.59         | ((sk_D) = (k1_xboole_0))
% 0.40/0.59         | ((sk_C) = (k1_xboole_0))
% 0.40/0.59         | ((sk_A) = (k1_xboole_0))
% 0.40/0.59         | ((sk_B) = (k1_xboole_0))))
% 0.40/0.59         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      (((((sk_B) = (k1_xboole_0))
% 0.40/0.59         | ((sk_A) = (k1_xboole_0))
% 0.40/0.59         | ((sk_C) = (k1_xboole_0))
% 0.40/0.59         | ((sk_D) = (k1_xboole_0))))
% 0.40/0.59         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('simplify', [status(thm)], ['28'])).
% 0.40/0.59  thf('30', plain,
% 0.40/0.59      ((((sk_D) != (k1_xboole_0))) <= (~ (((sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['7'])).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      (((((sk_D) != (sk_D))
% 0.40/0.59         | ((sk_C) = (k1_xboole_0))
% 0.40/0.59         | ((sk_A) = (k1_xboole_0))
% 0.40/0.59         | ((sk_B) = (k1_xboole_0))))
% 0.40/0.59         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.40/0.59             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.59  thf('32', plain,
% 0.40/0.59      (((((sk_B) = (k1_xboole_0))
% 0.40/0.59         | ((sk_A) = (k1_xboole_0))
% 0.40/0.59         | ((sk_C) = (k1_xboole_0))))
% 0.40/0.59         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.40/0.59             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('simplify', [status(thm)], ['31'])).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['5'])).
% 0.40/0.59  thf('34', plain,
% 0.40/0.59      (((((sk_C) != (sk_C))
% 0.40/0.59         | ((sk_A) = (k1_xboole_0))
% 0.40/0.59         | ((sk_B) = (k1_xboole_0))))
% 0.40/0.59         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.40/0.59             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.40/0.59             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.40/0.59  thf('35', plain,
% 0.40/0.59      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.40/0.59         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.40/0.59             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.40/0.59             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('simplify', [status(thm)], ['34'])).
% 0.40/0.59  thf('36', plain,
% 0.40/0.59      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['3'])).
% 0.40/0.59  thf('37', plain,
% 0.40/0.59      (((((sk_B) != (sk_B)) | ((sk_A) = (k1_xboole_0))))
% 0.40/0.59         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.40/0.59             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.40/0.59             ~ (((sk_B) = (k1_xboole_0))) & 
% 0.40/0.59             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      ((((sk_A) = (k1_xboole_0)))
% 0.40/0.59         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.40/0.59             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.40/0.59             ~ (((sk_B) = (k1_xboole_0))) & 
% 0.40/0.59             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('simplify', [status(thm)], ['37'])).
% 0.40/0.59  thf('39', plain,
% 0.40/0.59      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['0'])).
% 0.40/0.59  thf('40', plain,
% 0.40/0.59      ((((sk_A) != (sk_A)))
% 0.40/0.59         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.40/0.59             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.40/0.59             ~ (((sk_B) = (k1_xboole_0))) & 
% 0.40/0.59             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.40/0.59             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.59  thf('41', plain,
% 0.40/0.59      ((((sk_A) = (k1_xboole_0))) | 
% 0.40/0.59       ~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.40/0.59       (((sk_B) = (k1_xboole_0))) | (((sk_C) = (k1_xboole_0))) | 
% 0.40/0.59       (((sk_D) = (k1_xboole_0)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['40'])).
% 0.40/0.59  thf('42', plain,
% 0.40/0.59      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0)))),
% 0.40/0.59      inference('sat_resolution*', [status(thm)], ['2', '4', '6', '8', '41'])).
% 0.40/0.59  thf('43', plain,
% 0.40/0.59      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 0.40/0.59      inference('simpl_trail', [status(thm)], ['1', '42'])).
% 0.40/0.59  thf('44', plain,
% 0.40/0.59      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))
% 0.40/0.59        | ((sk_D) = (k1_xboole_0))
% 0.40/0.59        | ((sk_C) = (k1_xboole_0))
% 0.40/0.59        | ((sk_B) = (k1_xboole_0))
% 0.40/0.59        | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['44'])).
% 0.40/0.59  thf('46', plain,
% 0.40/0.59      ((((sk_D) = (k1_xboole_0))) <= ((((sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['44'])).
% 0.40/0.59  thf('47', plain,
% 0.40/0.59      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.40/0.59         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.40/0.59           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.40/0.59      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.40/0.59  thf('48', plain,
% 0.40/0.59      (![X1 : $i, X2 : $i]:
% 0.40/0.59         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.40/0.59  thf('49', plain,
% 0.40/0.59      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['48'])).
% 0.40/0.59  thf('50', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['47', '49'])).
% 0.40/0.59  thf('51', plain,
% 0.40/0.59      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59          ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D) = (k1_xboole_0)))
% 0.40/0.59         <= ((((sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup+', [status(thm)], ['46', '50'])).
% 0.40/0.59  thf('52', plain,
% 0.40/0.59      ((((sk_D) = (k1_xboole_0))) <= ((((sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['44'])).
% 0.40/0.59  thf('53', plain,
% 0.40/0.59      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59          ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D) = (sk_D)))
% 0.40/0.59         <= ((((sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('demod', [status(thm)], ['51', '52'])).
% 0.40/0.59  thf('54', plain,
% 0.40/0.59      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0)))
% 0.40/0.59         <= (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['0'])).
% 0.40/0.59  thf('55', plain,
% 0.40/0.59      ((((sk_D) != (k1_xboole_0)))
% 0.40/0.59         <= (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) & 
% 0.40/0.59             (((sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['53', '54'])).
% 0.40/0.59  thf('56', plain,
% 0.40/0.59      ((((sk_D) = (k1_xboole_0))) <= ((((sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['44'])).
% 0.40/0.59  thf('57', plain,
% 0.40/0.59      ((((sk_D) != (sk_D)))
% 0.40/0.59         <= (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) & 
% 0.40/0.59             (((sk_D) = (k1_xboole_0))))),
% 0.40/0.59      inference('demod', [status(thm)], ['55', '56'])).
% 0.40/0.59  thf('58', plain,
% 0.40/0.59      (~ (((sk_D) = (k1_xboole_0))) | 
% 0.40/0.59       (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['57'])).
% 0.40/0.59  thf('59', plain,
% 0.40/0.59      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['44'])).
% 0.40/0.59  thf('60', plain,
% 0.40/0.59      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.59         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.40/0.59           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.40/0.59  thf('61', plain,
% 0.40/0.59      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['48'])).
% 0.40/0.59  thf('62', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['60', '61'])).
% 0.40/0.59  thf('63', plain,
% 0.40/0.59      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.40/0.59         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.40/0.59           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.40/0.59      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.40/0.59  thf('64', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0)
% 0.40/0.59           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['62', '63'])).
% 0.40/0.59  thf('65', plain,
% 0.40/0.59      (![X1 : $i, X2 : $i]:
% 0.40/0.59         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.40/0.59  thf('66', plain,
% 0.40/0.59      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['65'])).
% 0.40/0.59  thf('67', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['64', '66'])).
% 0.40/0.59  thf('68', plain,
% 0.40/0.59      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59          ((k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0) = (k1_xboole_0)))
% 0.40/0.59         <= ((((sk_C) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup+', [status(thm)], ['59', '67'])).
% 0.40/0.59  thf('69', plain,
% 0.40/0.59      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['44'])).
% 0.40/0.59  thf('70', plain,
% 0.40/0.59      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59          ((k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0) = (sk_C)))
% 0.40/0.59         <= ((((sk_C) = (k1_xboole_0))))),
% 0.40/0.59      inference('demod', [status(thm)], ['68', '69'])).
% 0.40/0.59  thf('71', plain,
% 0.40/0.59      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 0.40/0.59      inference('simpl_trail', [status(thm)], ['1', '42'])).
% 0.40/0.59  thf('72', plain,
% 0.40/0.59      ((((sk_C) != (k1_xboole_0))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['70', '71'])).
% 0.40/0.59  thf('73', plain,
% 0.40/0.59      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['44'])).
% 0.40/0.59  thf('74', plain, ((((sk_C) != (sk_C))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.40/0.59      inference('demod', [status(thm)], ['72', '73'])).
% 0.40/0.59  thf('75', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['74'])).
% 0.40/0.59  thf('76', plain,
% 0.40/0.59      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['44'])).
% 0.40/0.59  thf('77', plain,
% 0.40/0.59      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['48'])).
% 0.40/0.59  thf('78', plain,
% 0.40/0.59      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.59         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.40/0.59           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.40/0.59  thf('79', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0)
% 0.40/0.59           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['77', '78'])).
% 0.40/0.59  thf('80', plain,
% 0.40/0.59      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['65'])).
% 0.40/0.59  thf('81', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['79', '80'])).
% 0.40/0.59  thf('82', plain,
% 0.40/0.59      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.40/0.59         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.40/0.59           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.40/0.59      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.40/0.59  thf('83', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0)
% 0.40/0.59           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['81', '82'])).
% 0.40/0.59  thf('84', plain,
% 0.40/0.59      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['65'])).
% 0.40/0.59  thf('85', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['83', '84'])).
% 0.40/0.59  thf('86', plain,
% 0.40/0.59      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59          ((k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0) = (k1_xboole_0)))
% 0.40/0.59         <= ((((sk_B) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup+', [status(thm)], ['76', '85'])).
% 0.40/0.59  thf('87', plain,
% 0.40/0.59      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['44'])).
% 0.40/0.59  thf('88', plain,
% 0.40/0.59      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59          ((k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0) = (sk_B)))
% 0.40/0.59         <= ((((sk_B) = (k1_xboole_0))))),
% 0.40/0.59      inference('demod', [status(thm)], ['86', '87'])).
% 0.40/0.59  thf('89', plain,
% 0.40/0.59      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 0.40/0.59      inference('simpl_trail', [status(thm)], ['1', '42'])).
% 0.40/0.59  thf('90', plain,
% 0.40/0.59      ((((sk_B) != (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['88', '89'])).
% 0.40/0.59  thf('91', plain,
% 0.40/0.59      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['44'])).
% 0.40/0.59  thf('92', plain, ((((sk_B) != (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.40/0.59      inference('demod', [status(thm)], ['90', '91'])).
% 0.40/0.59  thf('93', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['92'])).
% 0.40/0.59  thf('94', plain,
% 0.40/0.59      ((((sk_A) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0))) | 
% 0.40/0.59       (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.40/0.59       (((sk_C) = (k1_xboole_0))) | (((sk_D) = (k1_xboole_0)))),
% 0.40/0.59      inference('split', [status(esa)], ['44'])).
% 0.40/0.59  thf('95', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.40/0.59      inference('sat_resolution*', [status(thm)],
% 0.40/0.59                ['58', '75', '2', '4', '6', '8', '41', '93', '94'])).
% 0.40/0.59  thf('96', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.59      inference('simpl_trail', [status(thm)], ['45', '95'])).
% 0.40/0.59  thf('97', plain, (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['43', '96'])).
% 0.40/0.59  thf('98', plain,
% 0.40/0.59      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['44'])).
% 0.40/0.59  thf('99', plain,
% 0.40/0.59      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['65'])).
% 0.40/0.59  thf('100', plain,
% 0.40/0.59      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.59         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.40/0.59           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.40/0.59  thf('101', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0)
% 0.40/0.59           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['99', '100'])).
% 0.40/0.59  thf('102', plain,
% 0.40/0.59      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['65'])).
% 0.40/0.59  thf('103', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['101', '102'])).
% 0.40/0.59  thf('104', plain,
% 0.40/0.59      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.40/0.59         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.40/0.59           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.40/0.59      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.40/0.59  thf('105', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0)
% 0.40/0.59           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['103', '104'])).
% 0.40/0.59  thf('106', plain,
% 0.40/0.59      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['65'])).
% 0.40/0.59  thf('107', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0) = (k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['105', '106'])).
% 0.40/0.59  thf('108', plain,
% 0.40/0.59      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59          ((k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0) = (k1_xboole_0)))
% 0.40/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup+', [status(thm)], ['98', '107'])).
% 0.40/0.59  thf('109', plain,
% 0.40/0.59      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['44'])).
% 0.40/0.59  thf('110', plain,
% 0.40/0.59      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59          ((k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0) = (sk_A)))
% 0.40/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.40/0.59      inference('demod', [status(thm)], ['108', '109'])).
% 0.40/0.59  thf('111', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.40/0.59      inference('sat_resolution*', [status(thm)],
% 0.40/0.59                ['58', '75', '2', '4', '6', '8', '41', '93', '94'])).
% 0.40/0.59  thf('112', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0) = (sk_A))),
% 0.40/0.59      inference('simpl_trail', [status(thm)], ['110', '111'])).
% 0.40/0.59  thf('113', plain, (((sk_A) != (sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['97', '112'])).
% 0.40/0.59  thf('114', plain, ($false), inference('simplify', [status(thm)], ['113'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.40/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

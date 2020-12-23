%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pl6hZBA351

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:38 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 813 expanded)
%              Number of leaves         :   13 ( 189 expanded)
%              Depth                    :   25
%              Number of atoms          : 1089 (11241 expanded)
%              Number of equality atoms :  238 (2647 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

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

thf(t53_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,
    ( ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
       != k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('19',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( sk_D != k1_xboole_0 )
   <= ( sk_D != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('22',plain,
    ( ( ( sk_D != sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('25',plain,
    ( ( ( sk_C != sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('28',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','4','6','8','32'])).

thf('34',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('36',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('37',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('38',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('44',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','44'])).

thf('46',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
        = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','45'])).

thf('47',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('48',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
        = sk_C )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('50',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('52',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    sk_C != k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('55',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('56',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ X0 @ sk_D )
        = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ X0 @ sk_D )
        = sk_D )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D )
        = sk_D )
   <= ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('62',plain,
    ( ( sk_D != k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('64',plain,
    ( ( sk_D != sk_D )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    sk_D != k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_D != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('67',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('68',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('69',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('70',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0 )
        = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','77'])).

thf('79',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('80',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0 )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('82',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('84',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    sk_B != k1_xboole_0 ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('87',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['53','65','2','4','6','66','67','85','86'])).

thf('88',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['35','87'])).

thf('89',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != sk_A ),
    inference(demod,[status(thm)],['34','88'])).

thf('90',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('91',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('92',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['90','99'])).

thf('101',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('102',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['53','65','2','4','6','66','67','85','86'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0 )
      = sk_A ) ),
    inference(simpl_trail,[status(thm)],['102','103'])).

thf('105',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['89','104'])).

thf('106',plain,(
    $false ),
    inference(simplify,[status(thm)],['105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pl6hZBA351
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:08:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.64  % Solved by: fo/fo7.sh
% 0.47/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.64  % done 705 iterations in 0.199s
% 0.47/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.64  % SZS output start Refutation
% 0.47/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.64  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.47/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.64  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.47/0.64  thf(t55_mcart_1, conjecture,
% 0.47/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.64     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.47/0.64         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.47/0.64       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.47/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.64    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.64        ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.47/0.64            ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.47/0.64          ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ) )),
% 0.47/0.64    inference('cnf.neg', [status(esa)], [t55_mcart_1])).
% 0.47/0.64  thf('0', plain,
% 0.47/0.64      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))
% 0.47/0.64        | ((sk_A) != (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('1', plain,
% 0.47/0.64      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0)))
% 0.47/0.64         <= (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['0'])).
% 0.47/0.64  thf('2', plain,
% 0.47/0.64      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.47/0.64       ~ (((sk_A) = (k1_xboole_0)))),
% 0.47/0.64      inference('split', [status(esa)], ['0'])).
% 0.47/0.64  thf('3', plain,
% 0.47/0.64      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))
% 0.47/0.64        | ((sk_B) != (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('4', plain,
% 0.47/0.64      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.47/0.64       ~ (((sk_B) = (k1_xboole_0)))),
% 0.47/0.64      inference('split', [status(esa)], ['3'])).
% 0.47/0.64  thf('5', plain,
% 0.47/0.64      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))
% 0.47/0.64        | ((sk_C) != (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('6', plain,
% 0.47/0.64      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.47/0.64       ~ (((sk_C) = (k1_xboole_0)))),
% 0.47/0.64      inference('split', [status(esa)], ['5'])).
% 0.47/0.64  thf('7', plain,
% 0.47/0.64      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))
% 0.47/0.64        | ((sk_D) != (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('8', plain,
% 0.47/0.64      (~ (((sk_D) = (k1_xboole_0))) | 
% 0.47/0.64       ~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0)))),
% 0.47/0.64      inference('split', [status(esa)], ['7'])).
% 0.47/0.64  thf('9', plain,
% 0.47/0.64      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))
% 0.47/0.64        | ((sk_D) = (k1_xboole_0))
% 0.47/0.64        | ((sk_C) = (k1_xboole_0))
% 0.47/0.64        | ((sk_B) = (k1_xboole_0))
% 0.47/0.64        | ((sk_A) = (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('10', plain,
% 0.47/0.64      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0)))
% 0.47/0.64         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['9'])).
% 0.47/0.64  thf(t53_mcart_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.64     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.47/0.64       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ))).
% 0.47/0.64  thf('11', plain,
% 0.47/0.64      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.64         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.47/0.64           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12) @ 
% 0.47/0.64              X13))),
% 0.47/0.64      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.47/0.64  thf(d3_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.47/0.64       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.47/0.64  thf('12', plain,
% 0.47/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.64         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.47/0.64           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.47/0.64      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.47/0.64  thf('13', plain,
% 0.47/0.64      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.64         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.47/0.64           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.47/0.64      inference('demod', [status(thm)], ['11', '12'])).
% 0.47/0.64  thf(t113_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.64  thf('14', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (((X0) = (k1_xboole_0))
% 0.47/0.64          | ((X1) = (k1_xboole_0))
% 0.47/0.64          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.64  thf('15', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.64         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.47/0.64          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0))
% 0.47/0.64          | ((X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.64  thf('16', plain,
% 0.47/0.64      (((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.64         | ((sk_D) = (k1_xboole_0))
% 0.47/0.64         | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))))
% 0.47/0.64         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['10', '15'])).
% 0.47/0.64  thf('17', plain,
% 0.47/0.64      (((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 0.47/0.64         | ((sk_D) = (k1_xboole_0))))
% 0.47/0.64         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('simplify', [status(thm)], ['16'])).
% 0.47/0.64  thf(t35_mcart_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.47/0.64         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.47/0.64       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.47/0.64  thf('18', plain,
% 0.47/0.64      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.47/0.64         (((k3_zfmisc_1 @ X6 @ X7 @ X8) != (k1_xboole_0))
% 0.47/0.64          | ((X8) = (k1_xboole_0))
% 0.47/0.64          | ((X7) = (k1_xboole_0))
% 0.47/0.64          | ((X6) = (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.47/0.64  thf('19', plain,
% 0.47/0.64      (((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.64         | ((sk_D) = (k1_xboole_0))
% 0.47/0.64         | ((sk_A) = (k1_xboole_0))
% 0.47/0.64         | ((sk_B) = (k1_xboole_0))
% 0.47/0.64         | ((sk_C) = (k1_xboole_0))))
% 0.47/0.64         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.64  thf('20', plain,
% 0.47/0.64      (((((sk_C) = (k1_xboole_0))
% 0.47/0.64         | ((sk_B) = (k1_xboole_0))
% 0.47/0.64         | ((sk_A) = (k1_xboole_0))
% 0.47/0.64         | ((sk_D) = (k1_xboole_0))))
% 0.47/0.64         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('simplify', [status(thm)], ['19'])).
% 0.47/0.64  thf('21', plain,
% 0.47/0.64      ((((sk_D) != (k1_xboole_0))) <= (~ (((sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['7'])).
% 0.47/0.64  thf('22', plain,
% 0.47/0.64      (((((sk_D) != (sk_D))
% 0.47/0.64         | ((sk_A) = (k1_xboole_0))
% 0.47/0.64         | ((sk_B) = (k1_xboole_0))
% 0.47/0.64         | ((sk_C) = (k1_xboole_0))))
% 0.47/0.64         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.47/0.64             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.64  thf('23', plain,
% 0.47/0.64      (((((sk_C) = (k1_xboole_0))
% 0.47/0.64         | ((sk_B) = (k1_xboole_0))
% 0.47/0.64         | ((sk_A) = (k1_xboole_0))))
% 0.47/0.64         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.47/0.64             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('simplify', [status(thm)], ['22'])).
% 0.47/0.64  thf('24', plain,
% 0.47/0.64      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['5'])).
% 0.47/0.64  thf('25', plain,
% 0.47/0.64      (((((sk_C) != (sk_C))
% 0.47/0.64         | ((sk_A) = (k1_xboole_0))
% 0.47/0.64         | ((sk_B) = (k1_xboole_0))))
% 0.47/0.64         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.47/0.64             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.47/0.64             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.64  thf('26', plain,
% 0.47/0.64      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.47/0.64         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.47/0.64             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.47/0.64             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('simplify', [status(thm)], ['25'])).
% 0.47/0.64  thf('27', plain,
% 0.47/0.64      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['3'])).
% 0.47/0.64  thf('28', plain,
% 0.47/0.64      (((((sk_B) != (sk_B)) | ((sk_A) = (k1_xboole_0))))
% 0.47/0.64         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.47/0.64             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.47/0.64             ~ (((sk_B) = (k1_xboole_0))) & 
% 0.47/0.64             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['26', '27'])).
% 0.47/0.64  thf('29', plain,
% 0.47/0.64      ((((sk_A) = (k1_xboole_0)))
% 0.47/0.64         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.47/0.64             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.47/0.64             ~ (((sk_B) = (k1_xboole_0))) & 
% 0.47/0.64             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('simplify', [status(thm)], ['28'])).
% 0.47/0.64  thf('30', plain,
% 0.47/0.64      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['0'])).
% 0.47/0.64  thf('31', plain,
% 0.47/0.64      ((((sk_A) != (sk_A)))
% 0.47/0.64         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.47/0.64             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.47/0.64             ~ (((sk_B) = (k1_xboole_0))) & 
% 0.47/0.64             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.47/0.64             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.64  thf('32', plain,
% 0.47/0.64      ((((sk_A) = (k1_xboole_0))) | 
% 0.47/0.64       ~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.47/0.64       (((sk_B) = (k1_xboole_0))) | (((sk_C) = (k1_xboole_0))) | 
% 0.47/0.64       (((sk_D) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['31'])).
% 0.47/0.64  thf('33', plain,
% 0.47/0.64      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0)))),
% 0.47/0.64      inference('sat_resolution*', [status(thm)], ['2', '4', '6', '8', '32'])).
% 0.47/0.64  thf('34', plain,
% 0.47/0.64      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 0.47/0.64      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.47/0.64  thf('35', plain,
% 0.47/0.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['9'])).
% 0.47/0.64  thf('36', plain,
% 0.47/0.64      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['9'])).
% 0.47/0.64  thf('37', plain,
% 0.47/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.64         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.47/0.64           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.47/0.64      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.47/0.64  thf('38', plain,
% 0.47/0.64      (![X1 : $i, X2 : $i]:
% 0.47/0.64         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.64  thf('39', plain,
% 0.47/0.64      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['38'])).
% 0.47/0.64  thf('40', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['37', '39'])).
% 0.47/0.64  thf('41', plain,
% 0.47/0.64      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.64         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.47/0.64           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.47/0.64      inference('demod', [status(thm)], ['11', '12'])).
% 0.47/0.64  thf('42', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0)
% 0.47/0.64           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['40', '41'])).
% 0.47/0.64  thf('43', plain,
% 0.47/0.64      (![X1 : $i, X2 : $i]:
% 0.47/0.64         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.64  thf('44', plain,
% 0.47/0.64      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['43'])).
% 0.47/0.64  thf('45', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.64      inference('demod', [status(thm)], ['42', '44'])).
% 0.47/0.64  thf('46', plain,
% 0.47/0.64      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64          ((k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0) = (k1_xboole_0)))
% 0.47/0.64         <= ((((sk_C) = (k1_xboole_0))))),
% 0.47/0.64      inference('sup+', [status(thm)], ['36', '45'])).
% 0.47/0.64  thf('47', plain,
% 0.47/0.64      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['9'])).
% 0.47/0.64  thf('48', plain,
% 0.47/0.64      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64          ((k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0) = (sk_C)))
% 0.47/0.64         <= ((((sk_C) = (k1_xboole_0))))),
% 0.47/0.64      inference('demod', [status(thm)], ['46', '47'])).
% 0.47/0.64  thf('49', plain,
% 0.47/0.64      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 0.47/0.64      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.47/0.64  thf('50', plain,
% 0.47/0.64      ((((sk_C) != (k1_xboole_0))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['48', '49'])).
% 0.47/0.64  thf('51', plain,
% 0.47/0.64      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['9'])).
% 0.47/0.64  thf('52', plain, ((((sk_C) != (sk_C))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.47/0.64      inference('demod', [status(thm)], ['50', '51'])).
% 0.47/0.64  thf('53', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['52'])).
% 0.47/0.64  thf('54', plain,
% 0.47/0.64      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.64         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.47/0.64           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.47/0.64      inference('demod', [status(thm)], ['11', '12'])).
% 0.47/0.64  thf('55', plain,
% 0.47/0.64      ((((sk_D) = (k1_xboole_0))) <= ((((sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['9'])).
% 0.47/0.64  thf('56', plain,
% 0.47/0.64      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['38'])).
% 0.47/0.64  thf('57', plain,
% 0.47/0.64      ((![X0 : $i]: ((k2_zfmisc_1 @ X0 @ sk_D) = (k1_xboole_0)))
% 0.47/0.64         <= ((((sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('sup+', [status(thm)], ['55', '56'])).
% 0.47/0.64  thf('58', plain,
% 0.47/0.64      ((((sk_D) = (k1_xboole_0))) <= ((((sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['9'])).
% 0.47/0.64  thf('59', plain,
% 0.47/0.64      ((![X0 : $i]: ((k2_zfmisc_1 @ X0 @ sk_D) = (sk_D)))
% 0.47/0.64         <= ((((sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('demod', [status(thm)], ['57', '58'])).
% 0.47/0.64  thf('60', plain,
% 0.47/0.64      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64          ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D) = (sk_D)))
% 0.47/0.64         <= ((((sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('sup+', [status(thm)], ['54', '59'])).
% 0.47/0.64  thf('61', plain,
% 0.47/0.64      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 0.47/0.64      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.47/0.64  thf('62', plain,
% 0.47/0.64      ((((sk_D) != (k1_xboole_0))) <= ((((sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['60', '61'])).
% 0.47/0.64  thf('63', plain,
% 0.47/0.64      ((((sk_D) = (k1_xboole_0))) <= ((((sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['9'])).
% 0.47/0.64  thf('64', plain, ((((sk_D) != (sk_D))) <= ((((sk_D) = (k1_xboole_0))))),
% 0.47/0.64      inference('demod', [status(thm)], ['62', '63'])).
% 0.47/0.64  thf('65', plain, (~ (((sk_D) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['64'])).
% 0.47/0.64  thf('66', plain,
% 0.47/0.64      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.47/0.64       ~ (((sk_D) = (k1_xboole_0)))),
% 0.47/0.64      inference('split', [status(esa)], ['7'])).
% 0.47/0.64  thf('67', plain,
% 0.47/0.64      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.47/0.64       (((sk_A) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0))) | 
% 0.47/0.64       (((sk_C) = (k1_xboole_0))) | (((sk_D) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['31'])).
% 0.47/0.64  thf('68', plain,
% 0.47/0.64      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['9'])).
% 0.47/0.64  thf('69', plain,
% 0.47/0.64      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['38'])).
% 0.47/0.64  thf('70', plain,
% 0.47/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.64         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.47/0.64           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.47/0.64      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.47/0.64  thf('71', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0)
% 0.47/0.64           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['69', '70'])).
% 0.47/0.64  thf('72', plain,
% 0.47/0.64      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['43'])).
% 0.47/0.64  thf('73', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.64      inference('demod', [status(thm)], ['71', '72'])).
% 0.47/0.64  thf('74', plain,
% 0.47/0.64      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.64         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.47/0.64           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.47/0.64      inference('demod', [status(thm)], ['11', '12'])).
% 0.47/0.64  thf('75', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         ((k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0)
% 0.47/0.64           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['73', '74'])).
% 0.47/0.64  thf('76', plain,
% 0.47/0.64      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['43'])).
% 0.47/0.64  thf('77', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         ((k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.47/0.64      inference('demod', [status(thm)], ['75', '76'])).
% 0.47/0.64  thf('78', plain,
% 0.47/0.64      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64          ((k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0) = (k1_xboole_0)))
% 0.47/0.64         <= ((((sk_B) = (k1_xboole_0))))),
% 0.47/0.64      inference('sup+', [status(thm)], ['68', '77'])).
% 0.47/0.64  thf('79', plain,
% 0.47/0.64      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['9'])).
% 0.47/0.64  thf('80', plain,
% 0.47/0.64      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64          ((k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0) = (sk_B)))
% 0.47/0.64         <= ((((sk_B) = (k1_xboole_0))))),
% 0.47/0.64      inference('demod', [status(thm)], ['78', '79'])).
% 0.47/0.64  thf('81', plain,
% 0.47/0.64      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 0.47/0.64      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.47/0.64  thf('82', plain,
% 0.47/0.64      ((((sk_B) != (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['80', '81'])).
% 0.47/0.64  thf('83', plain,
% 0.47/0.64      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['9'])).
% 0.47/0.64  thf('84', plain, ((((sk_B) != (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.47/0.64      inference('demod', [status(thm)], ['82', '83'])).
% 0.47/0.64  thf('85', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['84'])).
% 0.47/0.64  thf('86', plain,
% 0.47/0.64      ((((sk_A) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0))) | 
% 0.47/0.64       (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.47/0.64       (((sk_D) = (k1_xboole_0))) | (((sk_C) = (k1_xboole_0)))),
% 0.47/0.64      inference('split', [status(esa)], ['9'])).
% 0.47/0.64  thf('87', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.47/0.64      inference('sat_resolution*', [status(thm)],
% 0.47/0.64                ['53', '65', '2', '4', '6', '66', '67', '85', '86'])).
% 0.47/0.64  thf('88', plain, (((sk_A) = (k1_xboole_0))),
% 0.47/0.64      inference('simpl_trail', [status(thm)], ['35', '87'])).
% 0.47/0.64  thf('89', plain, (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_A))),
% 0.47/0.64      inference('demod', [status(thm)], ['34', '88'])).
% 0.47/0.64  thf('90', plain,
% 0.47/0.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['9'])).
% 0.47/0.64  thf('91', plain,
% 0.47/0.64      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['43'])).
% 0.47/0.64  thf('92', plain,
% 0.47/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.64         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.47/0.64           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.47/0.64      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.47/0.64  thf('93', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0)
% 0.47/0.64           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['91', '92'])).
% 0.47/0.64  thf('94', plain,
% 0.47/0.64      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['43'])).
% 0.47/0.64  thf('95', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.47/0.64      inference('demod', [status(thm)], ['93', '94'])).
% 0.47/0.64  thf('96', plain,
% 0.47/0.64      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.64         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.47/0.64           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.47/0.64      inference('demod', [status(thm)], ['11', '12'])).
% 0.47/0.64  thf('97', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         ((k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0)
% 0.47/0.64           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['95', '96'])).
% 0.47/0.64  thf('98', plain,
% 0.47/0.64      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['43'])).
% 0.47/0.64  thf('99', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         ((k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0) = (k1_xboole_0))),
% 0.47/0.64      inference('demod', [status(thm)], ['97', '98'])).
% 0.47/0.64  thf('100', plain,
% 0.47/0.64      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64          ((k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0) = (k1_xboole_0)))
% 0.47/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.64      inference('sup+', [status(thm)], ['90', '99'])).
% 0.47/0.64  thf('101', plain,
% 0.47/0.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['9'])).
% 0.47/0.64  thf('102', plain,
% 0.47/0.64      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64          ((k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0) = (sk_A)))
% 0.47/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.64      inference('demod', [status(thm)], ['100', '101'])).
% 0.47/0.64  thf('103', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.47/0.64      inference('sat_resolution*', [status(thm)],
% 0.47/0.64                ['53', '65', '2', '4', '6', '66', '67', '85', '86'])).
% 0.47/0.64  thf('104', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         ((k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0) = (sk_A))),
% 0.47/0.64      inference('simpl_trail', [status(thm)], ['102', '103'])).
% 0.47/0.64  thf('105', plain, (((sk_A) != (sk_A))),
% 0.47/0.64      inference('demod', [status(thm)], ['89', '104'])).
% 0.47/0.64  thf('106', plain, ($false), inference('simplify', [status(thm)], ['105'])).
% 0.47/0.64  
% 0.47/0.64  % SZS output end Refutation
% 0.47/0.64  
% 0.50/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

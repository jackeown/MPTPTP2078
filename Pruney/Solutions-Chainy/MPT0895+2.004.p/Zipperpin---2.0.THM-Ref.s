%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fUmKs5TSf6

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:38 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 723 expanded)
%              Number of leaves         :   14 ( 167 expanded)
%              Depth                    :   27
%              Number of atoms          : 1138 (10182 expanded)
%              Number of equality atoms :  259 (2487 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) )
        = X9 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) )
        = X3 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) )
        = X3 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ( ( k2_relat_1 @ k1_xboole_0 )
        = sk_D )
      | ( sk_D = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','16'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('19',plain,
    ( ( ( k1_xboole_0 = sk_D )
      | ( sk_D = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( k1_xboole_0 = sk_D ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('22',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( k1_xboole_0 = sk_D )
      | ( sk_C = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( k1_xboole_0 = sk_D ) )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( sk_D != k1_xboole_0 )
   <= ( sk_D != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('25',plain,
    ( ( ( sk_D != sk_D )
      | ( sk_C = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('28',plain,
    ( ( ( sk_C != sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('31',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_D != k1_xboole_0 )
      & ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','4','6','8','35'])).

thf('37',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','36'])).

thf('38',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('41',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ X0 @ sk_D )
        = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','43'])).

thf('45',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ X0 @ sk_D )
        = sk_D )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D )
        = sk_D )
   <= ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','46'])).

thf('48',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
   <= ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ( sk_D != k1_xboole_0 )
   <= ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
       != k1_xboole_0 )
      & ( sk_D = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('51',plain,
    ( ( sk_D != sk_D )
   <= ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
       != k1_xboole_0 )
      & ( sk_D = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_D != k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('54',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('55',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','55'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('60',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0 )
        = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('63',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','36'])).

thf('65',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('67',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    sk_A != k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('70',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('71',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('72',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
        = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','75'])).

thf('77',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('78',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
        = sk_C )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','36'])).

thf('80',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('82',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    sk_C != k1_xboole_0 ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('85',plain,(
    sk_B = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['52','68','2','4','6','8','69','83','84'])).

thf('86',plain,(
    sk_B = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['39','85'])).

thf('87',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['37','86'])).

thf('88',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('89',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('90',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('93',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0 )
        = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','94'])).

thf('96',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('97',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0 )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    sk_B = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['52','68','2','4','6','8','69','83','84'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0 )
      = sk_B ) ),
    inference(simpl_trail,[status(thm)],['97','98'])).

thf('100',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['87','99'])).

thf('101',plain,(
    $false ),
    inference(simplify,[status(thm)],['100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fUmKs5TSf6
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 11:20:41 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.65/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.65/0.86  % Solved by: fo/fo7.sh
% 0.65/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.86  % done 711 iterations in 0.382s
% 0.65/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.65/0.86  % SZS output start Refutation
% 0.65/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.65/0.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.65/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.86  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.65/0.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.65/0.86  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.65/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.65/0.86  thf(sk_D_type, type, sk_D: $i).
% 0.65/0.86  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.65/0.86  thf(t55_mcart_1, conjecture,
% 0.65/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.86     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.65/0.86         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.65/0.86       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.65/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.86    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.86        ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.65/0.86            ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.65/0.86          ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ) )),
% 0.65/0.86    inference('cnf.neg', [status(esa)], [t55_mcart_1])).
% 0.65/0.86  thf('0', plain,
% 0.65/0.86      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))
% 0.65/0.86        | ((sk_A) != (k1_xboole_0)))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('1', plain,
% 0.65/0.86      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0)))
% 0.65/0.86         <= (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['0'])).
% 0.65/0.86  thf('2', plain,
% 0.65/0.86      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.65/0.86       ~ (((sk_A) = (k1_xboole_0)))),
% 0.65/0.86      inference('split', [status(esa)], ['0'])).
% 0.65/0.86  thf('3', plain,
% 0.65/0.86      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))
% 0.65/0.86        | ((sk_B) != (k1_xboole_0)))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('4', plain,
% 0.65/0.86      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.65/0.86       ~ (((sk_B) = (k1_xboole_0)))),
% 0.65/0.86      inference('split', [status(esa)], ['3'])).
% 0.65/0.86  thf('5', plain,
% 0.65/0.86      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))
% 0.65/0.86        | ((sk_C) != (k1_xboole_0)))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('6', plain,
% 0.65/0.86      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.65/0.86       ~ (((sk_C) = (k1_xboole_0)))),
% 0.65/0.86      inference('split', [status(esa)], ['5'])).
% 0.65/0.86  thf('7', plain,
% 0.65/0.86      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))
% 0.65/0.86        | ((sk_D) != (k1_xboole_0)))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('8', plain,
% 0.65/0.86      (~ (((sk_D) = (k1_xboole_0))) | 
% 0.65/0.86       ~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0)))),
% 0.65/0.86      inference('split', [status(esa)], ['7'])).
% 0.65/0.86  thf('9', plain,
% 0.65/0.86      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))
% 0.65/0.86        | ((sk_D) = (k1_xboole_0))
% 0.65/0.86        | ((sk_C) = (k1_xboole_0))
% 0.65/0.86        | ((sk_B) = (k1_xboole_0))
% 0.65/0.86        | ((sk_A) = (k1_xboole_0)))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('10', plain,
% 0.65/0.86      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0)))
% 0.65/0.86         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['9'])).
% 0.65/0.86  thf(t53_mcart_1, axiom,
% 0.65/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.86     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.65/0.86       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ))).
% 0.65/0.86  thf('11', plain,
% 0.65/0.86      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.65/0.86         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.65/0.86           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12) @ 
% 0.65/0.86              X13))),
% 0.65/0.86      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.65/0.86  thf(t195_relat_1, axiom,
% 0.65/0.86    (![A:$i,B:$i]:
% 0.65/0.86     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.65/0.86          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.65/0.86               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.65/0.86  thf('12', plain,
% 0.65/0.86      (![X8 : $i, X9 : $i]:
% 0.65/0.86         (((X8) = (k1_xboole_0))
% 0.65/0.86          | ((k2_relat_1 @ (k2_zfmisc_1 @ X8 @ X9)) = (X9))
% 0.65/0.86          | ((X9) = (k1_xboole_0)))),
% 0.65/0.86      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.65/0.86  thf('13', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.65/0.86         (((k2_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)) = (X0))
% 0.65/0.86          | ((X0) = (k1_xboole_0))
% 0.65/0.86          | ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1) = (k1_xboole_0)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['11', '12'])).
% 0.65/0.86  thf(t113_zfmisc_1, axiom,
% 0.65/0.86    (![A:$i,B:$i]:
% 0.65/0.86     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.65/0.86       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.65/0.86  thf('14', plain,
% 0.65/0.86      (![X2 : $i, X3 : $i]:
% 0.65/0.86         (((X2) = (k1_xboole_0))
% 0.65/0.86          | ((X3) = (k1_xboole_0))
% 0.65/0.86          | ((k2_zfmisc_1 @ X3 @ X2) != (k1_xboole_0)))),
% 0.65/0.86      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.65/0.86  thf('15', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.65/0.86         (((k1_xboole_0) != (k1_xboole_0))
% 0.65/0.86          | ((X3) = (k1_xboole_0))
% 0.65/0.86          | ((k2_relat_1 @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3)) = (X3))
% 0.65/0.86          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.65/0.86          | ((X0) = (k1_xboole_0)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['13', '14'])).
% 0.65/0.86  thf('16', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.65/0.86         (((X0) = (k1_xboole_0))
% 0.65/0.86          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.65/0.86          | ((k2_relat_1 @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3)) = (X3))
% 0.65/0.86          | ((X3) = (k1_xboole_0)))),
% 0.65/0.86      inference('simplify', [status(thm)], ['15'])).
% 0.65/0.86  thf('17', plain,
% 0.65/0.86      (((((k2_relat_1 @ k1_xboole_0) = (sk_D))
% 0.65/0.86         | ((sk_D) = (k1_xboole_0))
% 0.65/0.86         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.65/0.86         | ((sk_C) = (k1_xboole_0))))
% 0.65/0.86         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('sup+', [status(thm)], ['10', '16'])).
% 0.65/0.86  thf(t60_relat_1, axiom,
% 0.65/0.86    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.65/0.86     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.65/0.86  thf('18', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.65/0.86      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.65/0.86  thf('19', plain,
% 0.65/0.86      (((((k1_xboole_0) = (sk_D))
% 0.65/0.86         | ((sk_D) = (k1_xboole_0))
% 0.65/0.86         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.65/0.86         | ((sk_C) = (k1_xboole_0))))
% 0.65/0.86         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('demod', [status(thm)], ['17', '18'])).
% 0.65/0.86  thf('20', plain,
% 0.65/0.86      (((((sk_C) = (k1_xboole_0))
% 0.65/0.86         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.65/0.86         | ((k1_xboole_0) = (sk_D))))
% 0.65/0.86         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('simplify', [status(thm)], ['19'])).
% 0.65/0.86  thf('21', plain,
% 0.65/0.86      (![X2 : $i, X3 : $i]:
% 0.65/0.86         (((X2) = (k1_xboole_0))
% 0.65/0.86          | ((X3) = (k1_xboole_0))
% 0.65/0.86          | ((k2_zfmisc_1 @ X3 @ X2) != (k1_xboole_0)))),
% 0.65/0.86      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.65/0.86  thf('22', plain,
% 0.65/0.86      (((((k1_xboole_0) != (k1_xboole_0))
% 0.65/0.86         | ((k1_xboole_0) = (sk_D))
% 0.65/0.86         | ((sk_C) = (k1_xboole_0))
% 0.65/0.86         | ((sk_A) = (k1_xboole_0))
% 0.65/0.86         | ((sk_B) = (k1_xboole_0))))
% 0.65/0.86         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['20', '21'])).
% 0.65/0.86  thf('23', plain,
% 0.65/0.86      (((((sk_B) = (k1_xboole_0))
% 0.65/0.86         | ((sk_A) = (k1_xboole_0))
% 0.65/0.86         | ((sk_C) = (k1_xboole_0))
% 0.65/0.86         | ((k1_xboole_0) = (sk_D))))
% 0.65/0.86         <= ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('simplify', [status(thm)], ['22'])).
% 0.65/0.86  thf('24', plain,
% 0.65/0.86      ((((sk_D) != (k1_xboole_0))) <= (~ (((sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['7'])).
% 0.65/0.86  thf('25', plain,
% 0.65/0.86      (((((sk_D) != (sk_D))
% 0.65/0.86         | ((sk_C) = (k1_xboole_0))
% 0.65/0.86         | ((sk_A) = (k1_xboole_0))
% 0.65/0.86         | ((sk_B) = (k1_xboole_0))))
% 0.65/0.86         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.65/0.86             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['23', '24'])).
% 0.65/0.86  thf('26', plain,
% 0.65/0.86      (((((sk_B) = (k1_xboole_0))
% 0.65/0.86         | ((sk_A) = (k1_xboole_0))
% 0.65/0.86         | ((sk_C) = (k1_xboole_0))))
% 0.65/0.86         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.65/0.86             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('simplify', [status(thm)], ['25'])).
% 0.65/0.86  thf('27', plain,
% 0.65/0.86      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['5'])).
% 0.65/0.86  thf('28', plain,
% 0.65/0.86      (((((sk_C) != (sk_C))
% 0.65/0.86         | ((sk_A) = (k1_xboole_0))
% 0.65/0.86         | ((sk_B) = (k1_xboole_0))))
% 0.65/0.86         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.65/0.86             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.65/0.86             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['26', '27'])).
% 0.65/0.86  thf('29', plain,
% 0.65/0.86      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.65/0.86         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.65/0.86             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.65/0.86             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('simplify', [status(thm)], ['28'])).
% 0.65/0.86  thf('30', plain,
% 0.65/0.86      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['3'])).
% 0.65/0.86  thf('31', plain,
% 0.65/0.86      (((((sk_B) != (sk_B)) | ((sk_A) = (k1_xboole_0))))
% 0.65/0.86         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.65/0.86             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.65/0.86             ~ (((sk_B) = (k1_xboole_0))) & 
% 0.65/0.86             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['29', '30'])).
% 0.65/0.86  thf('32', plain,
% 0.65/0.86      ((((sk_A) = (k1_xboole_0)))
% 0.65/0.86         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.65/0.86             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.65/0.86             ~ (((sk_B) = (k1_xboole_0))) & 
% 0.65/0.86             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('simplify', [status(thm)], ['31'])).
% 0.65/0.86  thf('33', plain,
% 0.65/0.86      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['0'])).
% 0.65/0.86  thf('34', plain,
% 0.65/0.86      ((((sk_A) != (sk_A)))
% 0.65/0.86         <= (~ (((sk_D) = (k1_xboole_0))) & 
% 0.65/0.86             ~ (((sk_C) = (k1_xboole_0))) & 
% 0.65/0.86             ~ (((sk_B) = (k1_xboole_0))) & 
% 0.65/0.86             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.65/0.86             (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['32', '33'])).
% 0.65/0.86  thf('35', plain,
% 0.65/0.86      ((((sk_A) = (k1_xboole_0))) | 
% 0.65/0.86       ~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.65/0.86       (((sk_B) = (k1_xboole_0))) | (((sk_C) = (k1_xboole_0))) | 
% 0.65/0.86       (((sk_D) = (k1_xboole_0)))),
% 0.65/0.86      inference('simplify', [status(thm)], ['34'])).
% 0.65/0.86  thf('36', plain,
% 0.65/0.86      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0)))),
% 0.65/0.86      inference('sat_resolution*', [status(thm)], ['2', '4', '6', '8', '35'])).
% 0.65/0.86  thf('37', plain,
% 0.65/0.86      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 0.65/0.86      inference('simpl_trail', [status(thm)], ['1', '36'])).
% 0.65/0.86  thf('38', plain,
% 0.65/0.86      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))
% 0.65/0.86        | ((sk_D) = (k1_xboole_0))
% 0.65/0.86        | ((sk_C) = (k1_xboole_0))
% 0.65/0.86        | ((sk_B) = (k1_xboole_0))
% 0.65/0.86        | ((sk_A) = (k1_xboole_0)))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('39', plain,
% 0.65/0.86      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['38'])).
% 0.65/0.86  thf('40', plain,
% 0.65/0.86      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.65/0.86         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.65/0.86           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12) @ 
% 0.65/0.86              X13))),
% 0.65/0.86      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.65/0.86  thf('41', plain,
% 0.65/0.86      ((((sk_D) = (k1_xboole_0))) <= ((((sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['38'])).
% 0.65/0.86  thf('42', plain,
% 0.65/0.86      (![X3 : $i, X4 : $i]:
% 0.65/0.86         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.65/0.86      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.65/0.86  thf('43', plain,
% 0.65/0.86      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.65/0.86      inference('simplify', [status(thm)], ['42'])).
% 0.65/0.86  thf('44', plain,
% 0.65/0.86      ((![X0 : $i]: ((k2_zfmisc_1 @ X0 @ sk_D) = (k1_xboole_0)))
% 0.65/0.86         <= ((((sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('sup+', [status(thm)], ['41', '43'])).
% 0.65/0.86  thf('45', plain,
% 0.65/0.86      ((((sk_D) = (k1_xboole_0))) <= ((((sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['38'])).
% 0.65/0.86  thf('46', plain,
% 0.65/0.86      ((![X0 : $i]: ((k2_zfmisc_1 @ X0 @ sk_D) = (sk_D)))
% 0.65/0.86         <= ((((sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('demod', [status(thm)], ['44', '45'])).
% 0.65/0.86  thf('47', plain,
% 0.65/0.86      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.86          ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D) = (sk_D)))
% 0.65/0.86         <= ((((sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('sup+', [status(thm)], ['40', '46'])).
% 0.65/0.86  thf('48', plain,
% 0.65/0.86      ((((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0)))
% 0.65/0.86         <= (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['0'])).
% 0.65/0.86  thf('49', plain,
% 0.65/0.86      ((((sk_D) != (k1_xboole_0)))
% 0.65/0.86         <= (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) & 
% 0.65/0.86             (((sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['47', '48'])).
% 0.65/0.86  thf('50', plain,
% 0.65/0.86      ((((sk_D) = (k1_xboole_0))) <= ((((sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['38'])).
% 0.65/0.86  thf('51', plain,
% 0.65/0.86      ((((sk_D) != (sk_D)))
% 0.65/0.86         <= (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) & 
% 0.65/0.86             (((sk_D) = (k1_xboole_0))))),
% 0.65/0.86      inference('demod', [status(thm)], ['49', '50'])).
% 0.65/0.86  thf('52', plain,
% 0.65/0.86      (~ (((sk_D) = (k1_xboole_0))) | 
% 0.65/0.86       (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0)))),
% 0.65/0.86      inference('simplify', [status(thm)], ['51'])).
% 0.65/0.86  thf('53', plain,
% 0.65/0.86      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['38'])).
% 0.65/0.86  thf('54', plain,
% 0.65/0.86      (![X3 : $i, X4 : $i]:
% 0.65/0.86         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.65/0.86      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.65/0.86  thf('55', plain,
% 0.65/0.86      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.65/0.86      inference('simplify', [status(thm)], ['54'])).
% 0.65/0.86  thf('56', plain,
% 0.65/0.86      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (k1_xboole_0)))
% 0.65/0.86         <= ((((sk_A) = (k1_xboole_0))))),
% 0.65/0.86      inference('sup+', [status(thm)], ['53', '55'])).
% 0.65/0.86  thf('57', plain,
% 0.65/0.86      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['38'])).
% 0.65/0.86  thf('58', plain,
% 0.65/0.86      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (sk_A)))
% 0.65/0.86         <= ((((sk_A) = (k1_xboole_0))))),
% 0.65/0.86      inference('demod', [status(thm)], ['56', '57'])).
% 0.65/0.86  thf('59', plain,
% 0.65/0.86      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.65/0.86         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.65/0.86           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12) @ 
% 0.65/0.86              X13))),
% 0.65/0.86      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.65/0.86  thf('60', plain,
% 0.65/0.86      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.86          ((k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0)
% 0.65/0.86            = (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1) @ X0)))
% 0.65/0.86         <= ((((sk_A) = (k1_xboole_0))))),
% 0.65/0.86      inference('sup+', [status(thm)], ['58', '59'])).
% 0.65/0.86  thf('61', plain,
% 0.65/0.86      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (sk_A)))
% 0.65/0.86         <= ((((sk_A) = (k1_xboole_0))))),
% 0.65/0.86      inference('demod', [status(thm)], ['56', '57'])).
% 0.65/0.86  thf('62', plain,
% 0.65/0.86      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (sk_A)))
% 0.65/0.86         <= ((((sk_A) = (k1_xboole_0))))),
% 0.65/0.86      inference('demod', [status(thm)], ['56', '57'])).
% 0.65/0.86  thf('63', plain,
% 0.65/0.86      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.86          ((k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0) = (sk_A)))
% 0.65/0.86         <= ((((sk_A) = (k1_xboole_0))))),
% 0.65/0.86      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.65/0.86  thf('64', plain,
% 0.65/0.86      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 0.65/0.86      inference('simpl_trail', [status(thm)], ['1', '36'])).
% 0.65/0.86  thf('65', plain,
% 0.65/0.86      ((((sk_A) != (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['63', '64'])).
% 0.65/0.86  thf('66', plain,
% 0.65/0.86      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['38'])).
% 0.65/0.86  thf('67', plain, ((((sk_A) != (sk_A))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.65/0.86      inference('demod', [status(thm)], ['65', '66'])).
% 0.65/0.86  thf('68', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.65/0.86      inference('simplify', [status(thm)], ['67'])).
% 0.65/0.86  thf('69', plain,
% 0.65/0.86      (~ (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.65/0.86       (((sk_A) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0))) | 
% 0.65/0.86       (((sk_C) = (k1_xboole_0))) | (((sk_D) = (k1_xboole_0)))),
% 0.65/0.86      inference('simplify', [status(thm)], ['34'])).
% 0.65/0.86  thf('70', plain,
% 0.65/0.86      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['38'])).
% 0.65/0.86  thf('71', plain,
% 0.65/0.86      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.65/0.86      inference('simplify', [status(thm)], ['42'])).
% 0.65/0.86  thf('72', plain,
% 0.65/0.86      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.65/0.86         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.65/0.86           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12) @ 
% 0.65/0.86              X13))),
% 0.65/0.86      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.65/0.86  thf('73', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.86         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0)
% 0.65/0.86           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['71', '72'])).
% 0.65/0.86  thf('74', plain,
% 0.65/0.86      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.65/0.86      inference('simplify', [status(thm)], ['54'])).
% 0.65/0.86  thf('75', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.86         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.65/0.86      inference('demod', [status(thm)], ['73', '74'])).
% 0.65/0.86  thf('76', plain,
% 0.65/0.86      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.86          ((k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0) = (k1_xboole_0)))
% 0.65/0.86         <= ((((sk_C) = (k1_xboole_0))))),
% 0.65/0.86      inference('sup+', [status(thm)], ['70', '75'])).
% 0.65/0.86  thf('77', plain,
% 0.65/0.86      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['38'])).
% 0.65/0.86  thf('78', plain,
% 0.65/0.86      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.86          ((k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0) = (sk_C)))
% 0.65/0.86         <= ((((sk_C) = (k1_xboole_0))))),
% 0.65/0.86      inference('demod', [status(thm)], ['76', '77'])).
% 0.65/0.86  thf('79', plain,
% 0.65/0.86      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 0.65/0.86      inference('simpl_trail', [status(thm)], ['1', '36'])).
% 0.65/0.86  thf('80', plain,
% 0.65/0.86      ((((sk_C) != (k1_xboole_0))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['78', '79'])).
% 0.65/0.86  thf('81', plain,
% 0.65/0.86      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['38'])).
% 0.65/0.86  thf('82', plain, ((((sk_C) != (sk_C))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.65/0.86      inference('demod', [status(thm)], ['80', '81'])).
% 0.65/0.86  thf('83', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.65/0.86      inference('simplify', [status(thm)], ['82'])).
% 0.65/0.86  thf('84', plain,
% 0.65/0.86      ((((sk_B) = (k1_xboole_0))) | (((sk_C) = (k1_xboole_0))) | 
% 0.65/0.86       (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))) | 
% 0.65/0.86       (((sk_A) = (k1_xboole_0))) | (((sk_D) = (k1_xboole_0)))),
% 0.65/0.86      inference('split', [status(esa)], ['38'])).
% 0.65/0.86  thf('85', plain, ((((sk_B) = (k1_xboole_0)))),
% 0.65/0.86      inference('sat_resolution*', [status(thm)],
% 0.65/0.86                ['52', '68', '2', '4', '6', '8', '69', '83', '84'])).
% 0.65/0.86  thf('86', plain, (((sk_B) = (k1_xboole_0))),
% 0.65/0.86      inference('simpl_trail', [status(thm)], ['39', '85'])).
% 0.65/0.86  thf('87', plain, (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_B))),
% 0.65/0.86      inference('demod', [status(thm)], ['37', '86'])).
% 0.65/0.86  thf('88', plain,
% 0.65/0.86      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['38'])).
% 0.65/0.86  thf('89', plain,
% 0.65/0.86      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.65/0.86      inference('simplify', [status(thm)], ['42'])).
% 0.65/0.86  thf('90', plain,
% 0.65/0.86      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.65/0.86         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.65/0.86           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12) @ 
% 0.65/0.86              X13))),
% 0.65/0.86      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.65/0.86  thf('91', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.86         ((k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0)
% 0.65/0.86           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1) @ X0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['89', '90'])).
% 0.65/0.86  thf('92', plain,
% 0.65/0.86      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.65/0.86      inference('simplify', [status(thm)], ['54'])).
% 0.65/0.86  thf('93', plain,
% 0.65/0.86      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.65/0.86      inference('simplify', [status(thm)], ['54'])).
% 0.65/0.86  thf('94', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.86         ((k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.65/0.86      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.65/0.86  thf('95', plain,
% 0.65/0.86      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.86          ((k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0) = (k1_xboole_0)))
% 0.65/0.86         <= ((((sk_B) = (k1_xboole_0))))),
% 0.65/0.86      inference('sup+', [status(thm)], ['88', '94'])).
% 0.65/0.86  thf('96', plain,
% 0.65/0.86      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['38'])).
% 0.65/0.86  thf('97', plain,
% 0.65/0.86      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.86          ((k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0) = (sk_B)))
% 0.65/0.86         <= ((((sk_B) = (k1_xboole_0))))),
% 0.65/0.86      inference('demod', [status(thm)], ['95', '96'])).
% 0.65/0.86  thf('98', plain, ((((sk_B) = (k1_xboole_0)))),
% 0.65/0.86      inference('sat_resolution*', [status(thm)],
% 0.65/0.86                ['52', '68', '2', '4', '6', '8', '69', '83', '84'])).
% 0.65/0.86  thf('99', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.86         ((k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0) = (sk_B))),
% 0.65/0.86      inference('simpl_trail', [status(thm)], ['97', '98'])).
% 0.65/0.86  thf('100', plain, (((sk_B) != (sk_B))),
% 0.65/0.86      inference('demod', [status(thm)], ['87', '99'])).
% 0.65/0.86  thf('101', plain, ($false), inference('simplify', [status(thm)], ['100'])).
% 0.65/0.86  
% 0.65/0.86  % SZS output end Refutation
% 0.65/0.86  
% 0.65/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

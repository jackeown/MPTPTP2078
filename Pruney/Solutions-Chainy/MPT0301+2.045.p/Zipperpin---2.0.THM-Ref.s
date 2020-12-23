%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2nZq3litbr

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:05 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 819 expanded)
%              Number of leaves         :   24 ( 231 expanded)
%              Depth                    :   22
%              Number of atoms          : 1198 (7546 expanded)
%              Number of equality atoms :  177 (1208 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i )).

thf(t113_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
      <=> ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_zfmisc_1])).

thf('0',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('3',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t104_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ~ ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ B @ C ) @ ( k2_zfmisc_1 @ D @ E ) ) )
        & ! [F: $i,G: $i] :
            ~ ( ( A
                = ( k4_tarski @ F @ G ) )
              & ( r2_hidden @ F @ ( k3_xboole_0 @ B @ D ) )
              & ( r2_hidden @ G @ ( k3_xboole_0 @ C @ E ) ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( r2_hidden @ ( sk_F @ X31 @ X30 @ X29 @ X28 @ X27 ) @ ( k3_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t104_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X4 )
      | ( r2_hidden @ ( sk_F @ X0 @ X1 @ X2 @ X3 @ ( sk_C @ X4 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) @ ( k3_xboole_0 @ X3 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X3 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) ) @ X4 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X3 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ X2 ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X20: $i] :
      ( ( X20
        = ( k3_tarski @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X20 @ X16 ) @ X16 )
      | ( r2_hidden @ ( sk_C_2 @ X20 @ X16 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('18',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_A )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_A )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('25',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ sk_A )
        | ~ ( r1_xboole_0 @ X0 @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('27',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('28',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ! [X1: $i] :
        ~ ( r2_hidden @ X1 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C_2 @ X0 @ sk_A ) @ X0 )
        | ( X0
          = ( k3_tarski @ sk_A ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','29'])).

thf('31',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('32',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('33',plain,
    ( ( ( k3_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('35',plain,
    ( ( ( k3_tarski @ sk_A )
      = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C_2 @ X0 @ sk_A ) @ X0 )
        | ( X0 = sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('38',plain,(
    ! [X16: $i,X20: $i] :
      ( ( X20
        = ( k3_tarski @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X20 @ X16 ) @ X16 )
      | ( r2_hidden @ ( sk_C_2 @ X20 @ X16 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('39',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('40',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('43',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ ( sk_C_2 @ X1 @ sk_A ) @ X0 )
        | ~ ( r1_xboole_0 @ X1 @ X0 )
        | ( X1 = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('51',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ ( sk_C_2 @ X1 @ sk_A ) @ X0 )
        | ~ ( r1_xboole_0 @ X1 @ X0 )
        | ( X1 = sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( X0 = sk_A )
        | ( X0 = sk_A )
        | ~ ( r1_xboole_0 @ X0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ X0 )
        | ( X0 = sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','53'])).

thf('55',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('60',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('67',plain,(
    ! [X22: $i,X23: $i,X24: $i,X26: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ ( k2_zfmisc_1 @ X23 @ X26 ) )
      | ~ ( r2_hidden @ X24 @ X26 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ ( sk_C_2 @ X1 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ sk_A @ k1_xboole_0 ) @ ( sk_C_2 @ sk_B @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('72',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('74',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('77',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','61','63','78'])).

thf('80',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','79'])).

thf('81',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('82',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('83',plain,(
    sk_B = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','61','63','78','82'])).

thf('84',plain,(
    sk_B = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['81','83'])).

thf('85',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != sk_B ),
    inference(demod,[status(thm)],['80','84'])).

thf('86',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('87',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('88',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    sk_B = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','61','63','78','82'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('92',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( r2_hidden @ ( sk_G @ X31 @ X30 @ X29 @ X28 @ X27 ) @ ( k3_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t104_zfmisc_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_G @ X0 @ X1 @ X2 @ X3 @ ( sk_C_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X3 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,(
    ! [X16: $i,X20: $i] :
      ( ( X20
        = ( k3_tarski @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X20 @ X16 ) @ X16 )
      | ( r2_hidden @ ( sk_C_2 @ X20 @ X16 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('98',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('99',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_B )
        = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_B )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('104',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ sk_B )
        | ~ ( r1_xboole_0 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('106',plain,
    ( ! [X1: $i] :
        ~ ( r2_hidden @ X1 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C_2 @ X0 @ sk_B ) @ X0 )
        | ( X0
          = ( k3_tarski @ sk_B ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','106'])).

thf('108',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('109',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('110',plain,
    ( ( ( k3_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('112',plain,
    ( ( ( k3_tarski @ sk_B )
      = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C_2 @ X0 @ sk_B ) @ X0 )
        | ( X0 = sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['107','112'])).

thf('114',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('116',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ ( sk_C_2 @ X1 @ sk_B ) @ X0 )
        | ~ ( r1_xboole_0 @ X1 @ X0 )
        | ( X1 = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('118',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ ( sk_C_2 @ X1 @ sk_B ) @ X0 )
        | ~ ( r1_xboole_0 @ X1 @ X0 )
        | ( X1 = sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ! [X0: $i] :
        ( ( X0 = sk_B )
        | ( X0 = sk_B )
        | ~ ( r1_xboole_0 @ X0 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('120',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ X0 )
        | ( X0 = sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    sk_B = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','61','63','78','82'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['96','122'])).

thf('124',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['85','123'])).

thf('125',plain,(
    $false ),
    inference(simplify,[status(thm)],['124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2nZq3litbr
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:42:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.60/1.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.60/1.78  % Solved by: fo/fo7.sh
% 1.60/1.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.60/1.78  % done 1641 iterations in 1.307s
% 1.60/1.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.60/1.78  % SZS output start Refutation
% 1.60/1.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.60/1.78  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 1.60/1.78  thf(sk_B_type, type, sk_B: $i).
% 1.60/1.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.60/1.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.60/1.78  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.60/1.78  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.60/1.78  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 1.60/1.78  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.60/1.78  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.60/1.78  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.60/1.78  thf(sk_A_type, type, sk_A: $i).
% 1.60/1.78  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.60/1.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.60/1.78  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i).
% 1.60/1.78  thf(t113_zfmisc_1, conjecture,
% 1.60/1.78    (![A:$i,B:$i]:
% 1.60/1.78     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.60/1.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.60/1.78  thf(zf_stmt_0, negated_conjecture,
% 1.60/1.78    (~( ![A:$i,B:$i]:
% 1.60/1.78        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.60/1.78          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 1.60/1.78    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 1.60/1.78  thf('0', plain,
% 1.60/1.78      ((((sk_A) != (k1_xboole_0))
% 1.60/1.78        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('1', plain,
% 1.60/1.78      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 1.60/1.78         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['0'])).
% 1.60/1.78  thf('2', plain,
% 1.60/1.78      (~ (((sk_A) = (k1_xboole_0))) | 
% 1.60/1.78       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.60/1.78      inference('split', [status(esa)], ['0'])).
% 1.60/1.78  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.60/1.78  thf('3', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 1.60/1.78      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.60/1.78  thf(t3_xboole_0, axiom,
% 1.60/1.78    (![A:$i,B:$i]:
% 1.60/1.78     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.60/1.78            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.60/1.78       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.60/1.78            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.60/1.78  thf('4', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 1.60/1.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.60/1.78  thf(t104_zfmisc_1, axiom,
% 1.60/1.78    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.60/1.78     ( ~( ( r2_hidden @
% 1.60/1.78            A @ 
% 1.60/1.78            ( k3_xboole_0 @ ( k2_zfmisc_1 @ B @ C ) @ ( k2_zfmisc_1 @ D @ E ) ) ) & 
% 1.60/1.78          ( ![F:$i,G:$i]:
% 1.60/1.78            ( ~( ( ( A ) = ( k4_tarski @ F @ G ) ) & 
% 1.60/1.78                 ( r2_hidden @ F @ ( k3_xboole_0 @ B @ D ) ) & 
% 1.60/1.78                 ( r2_hidden @ G @ ( k3_xboole_0 @ C @ E ) ) ) ) ) ) ))).
% 1.60/1.78  thf('5', plain,
% 1.60/1.78      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.60/1.78         (~ (r2_hidden @ X27 @ 
% 1.60/1.78             (k3_xboole_0 @ (k2_zfmisc_1 @ X28 @ X29) @ 
% 1.60/1.78              (k2_zfmisc_1 @ X30 @ X31)))
% 1.60/1.78          | (r2_hidden @ (sk_F @ X31 @ X30 @ X29 @ X28 @ X27) @ 
% 1.60/1.78             (k3_xboole_0 @ X28 @ X30)))),
% 1.60/1.78      inference('cnf', [status(esa)], [t104_zfmisc_1])).
% 1.60/1.78  thf('6', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.60/1.78         ((r1_xboole_0 @ 
% 1.60/1.78           (k3_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0)) @ 
% 1.60/1.78           X4)
% 1.60/1.78          | (r2_hidden @ 
% 1.60/1.78             (sk_F @ X0 @ X1 @ X2 @ X3 @ 
% 1.60/1.78              (sk_C @ X4 @ 
% 1.60/1.78               (k3_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0)))) @ 
% 1.60/1.78             (k3_xboole_0 @ X3 @ X1)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['4', '5'])).
% 1.60/1.78  thf(t4_xboole_0, axiom,
% 1.60/1.78    (![A:$i,B:$i]:
% 1.60/1.78     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.60/1.78            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.60/1.78       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.60/1.78            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.60/1.78  thf('7', plain,
% 1.60/1.78      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.60/1.78         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 1.60/1.78          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.60/1.78      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.60/1.78  thf('8', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.60/1.78         ((r1_xboole_0 @ 
% 1.60/1.78           (k3_xboole_0 @ (k2_zfmisc_1 @ X1 @ X3) @ (k2_zfmisc_1 @ X0 @ X2)) @ 
% 1.60/1.78           X4)
% 1.60/1.78          | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['6', '7'])).
% 1.60/1.78  thf('9', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.60/1.78         (r1_xboole_0 @ 
% 1.60/1.78          (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X3) @ 
% 1.60/1.78           (k2_zfmisc_1 @ k1_xboole_0 @ X2)) @ 
% 1.60/1.78          X1)),
% 1.60/1.78      inference('sup-', [status(thm)], ['3', '8'])).
% 1.60/1.78  thf('10', plain,
% 1.60/1.78      (![X4 : $i, X5 : $i]:
% 1.60/1.78         ((r1_xboole_0 @ X4 @ X5)
% 1.60/1.78          | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 1.60/1.78      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.60/1.78  thf('11', plain,
% 1.60/1.78      (![X4 : $i, X5 : $i]:
% 1.60/1.78         ((r1_xboole_0 @ X4 @ X5)
% 1.60/1.78          | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 1.60/1.78      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.60/1.78  thf('12', plain,
% 1.60/1.78      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.60/1.78         (~ (r2_hidden @ X2 @ X0)
% 1.60/1.78          | ~ (r2_hidden @ X2 @ X3)
% 1.60/1.78          | ~ (r1_xboole_0 @ X0 @ X3))),
% 1.60/1.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.60/1.78  thf('13', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.78         ((r1_xboole_0 @ X1 @ X0)
% 1.60/1.78          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.60/1.78          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 1.60/1.78      inference('sup-', [status(thm)], ['11', '12'])).
% 1.60/1.78  thf('14', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         ((r1_xboole_0 @ X1 @ X0)
% 1.60/1.78          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.60/1.78          | (r1_xboole_0 @ X1 @ X0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['10', '13'])).
% 1.60/1.78  thf('15', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.60/1.78          | (r1_xboole_0 @ X1 @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['14'])).
% 1.60/1.78  thf('16', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.78         (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ 
% 1.60/1.78          (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['9', '15'])).
% 1.60/1.78  thf(d4_tarski, axiom,
% 1.60/1.78    (![A:$i,B:$i]:
% 1.60/1.78     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 1.60/1.78       ( ![C:$i]:
% 1.60/1.78         ( ( r2_hidden @ C @ B ) <=>
% 1.60/1.78           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 1.60/1.78  thf('17', plain,
% 1.60/1.78      (![X16 : $i, X20 : $i]:
% 1.60/1.78         (((X20) = (k3_tarski @ X16))
% 1.60/1.78          | (r2_hidden @ (sk_D @ X20 @ X16) @ X16)
% 1.60/1.78          | (r2_hidden @ (sk_C_2 @ X20 @ X16) @ X20))),
% 1.60/1.78      inference('cnf', [status(esa)], [d4_tarski])).
% 1.60/1.78  thf('18', plain,
% 1.60/1.78      ((((sk_B) = (k1_xboole_0))
% 1.60/1.78        | ((sk_A) = (k1_xboole_0))
% 1.60/1.78        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('19', plain,
% 1.60/1.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf(t2_boole, axiom,
% 1.60/1.78    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.60/1.78  thf('20', plain,
% 1.60/1.78      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.60/1.78      inference('cnf', [status(esa)], [t2_boole])).
% 1.60/1.78  thf('21', plain,
% 1.60/1.78      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_A) = (k1_xboole_0)))
% 1.60/1.78         <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup+', [status(thm)], ['19', '20'])).
% 1.60/1.78  thf('22', plain,
% 1.60/1.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf('23', plain,
% 1.60/1.78      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_A) = (sk_A)))
% 1.60/1.78         <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('demod', [status(thm)], ['21', '22'])).
% 1.60/1.78  thf('24', plain,
% 1.60/1.78      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.60/1.78         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 1.60/1.78          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.60/1.78      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.60/1.78  thf('25', plain,
% 1.60/1.78      ((![X0 : $i, X1 : $i]:
% 1.60/1.78          (~ (r2_hidden @ X1 @ sk_A) | ~ (r1_xboole_0 @ X0 @ sk_A)))
% 1.60/1.78         <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['23', '24'])).
% 1.60/1.78  thf('26', plain,
% 1.60/1.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf('27', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 1.60/1.78      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.60/1.78  thf('28', plain,
% 1.60/1.78      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup+', [status(thm)], ['26', '27'])).
% 1.60/1.78  thf('29', plain,
% 1.60/1.78      ((![X1 : $i]: ~ (r2_hidden @ X1 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('demod', [status(thm)], ['25', '28'])).
% 1.60/1.78  thf('30', plain,
% 1.60/1.78      ((![X0 : $i]:
% 1.60/1.78          ((r2_hidden @ (sk_C_2 @ X0 @ sk_A) @ X0)
% 1.60/1.78           | ((X0) = (k3_tarski @ sk_A))))
% 1.60/1.78         <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['17', '29'])).
% 1.60/1.78  thf('31', plain,
% 1.60/1.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 1.60/1.78  thf('32', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 1.60/1.78      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 1.60/1.78  thf('33', plain,
% 1.60/1.78      ((((k3_tarski @ sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup+', [status(thm)], ['31', '32'])).
% 1.60/1.78  thf('34', plain,
% 1.60/1.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf('35', plain,
% 1.60/1.78      ((((k3_tarski @ sk_A) = (sk_A))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('demod', [status(thm)], ['33', '34'])).
% 1.60/1.78  thf('36', plain,
% 1.60/1.78      ((![X0 : $i]: ((r2_hidden @ (sk_C_2 @ X0 @ sk_A) @ X0) | ((X0) = (sk_A))))
% 1.60/1.78         <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('demod', [status(thm)], ['30', '35'])).
% 1.60/1.78  thf('37', plain,
% 1.60/1.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf('38', plain,
% 1.60/1.78      (![X16 : $i, X20 : $i]:
% 1.60/1.78         (((X20) = (k3_tarski @ X16))
% 1.60/1.78          | (r2_hidden @ (sk_D @ X20 @ X16) @ X16)
% 1.60/1.78          | (r2_hidden @ (sk_C_2 @ X20 @ X16) @ X20))),
% 1.60/1.78      inference('cnf', [status(esa)], [d4_tarski])).
% 1.60/1.78  thf('39', plain,
% 1.60/1.78      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.60/1.78      inference('cnf', [status(esa)], [t2_boole])).
% 1.60/1.78  thf('40', plain,
% 1.60/1.78      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.60/1.78         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 1.60/1.78          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.60/1.78      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.60/1.78  thf('41', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['39', '40'])).
% 1.60/1.78  thf('42', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 1.60/1.78      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.60/1.78  thf('43', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.60/1.78      inference('demod', [status(thm)], ['41', '42'])).
% 1.60/1.78  thf('44', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 1.60/1.78          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['38', '43'])).
% 1.60/1.78  thf('45', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 1.60/1.78      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 1.60/1.78  thf('46', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 1.60/1.78          | ((X0) = (k1_xboole_0)))),
% 1.60/1.78      inference('demod', [status(thm)], ['44', '45'])).
% 1.60/1.78  thf('47', plain,
% 1.60/1.78      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.60/1.78         (~ (r2_hidden @ X2 @ X0)
% 1.60/1.78          | ~ (r2_hidden @ X2 @ X3)
% 1.60/1.78          | ~ (r1_xboole_0 @ X0 @ X3))),
% 1.60/1.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.60/1.78  thf('48', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         (((X0) = (k1_xboole_0))
% 1.60/1.78          | ~ (r1_xboole_0 @ X0 @ X1)
% 1.60/1.78          | ~ (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X1))),
% 1.60/1.78      inference('sup-', [status(thm)], ['46', '47'])).
% 1.60/1.78  thf('49', plain,
% 1.60/1.78      ((![X0 : $i, X1 : $i]:
% 1.60/1.78          (~ (r2_hidden @ (sk_C_2 @ X1 @ sk_A) @ X0)
% 1.60/1.78           | ~ (r1_xboole_0 @ X1 @ X0)
% 1.60/1.78           | ((X1) = (k1_xboole_0))))
% 1.60/1.78         <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['37', '48'])).
% 1.60/1.78  thf('50', plain,
% 1.60/1.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf('51', plain,
% 1.60/1.78      ((![X0 : $i, X1 : $i]:
% 1.60/1.78          (~ (r2_hidden @ (sk_C_2 @ X1 @ sk_A) @ X0)
% 1.60/1.78           | ~ (r1_xboole_0 @ X1 @ X0)
% 1.60/1.78           | ((X1) = (sk_A))))
% 1.60/1.78         <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('demod', [status(thm)], ['49', '50'])).
% 1.60/1.78  thf('52', plain,
% 1.60/1.78      ((![X0 : $i]:
% 1.60/1.78          (((X0) = (sk_A)) | ((X0) = (sk_A)) | ~ (r1_xboole_0 @ X0 @ X0)))
% 1.60/1.78         <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['36', '51'])).
% 1.60/1.78  thf('53', plain,
% 1.60/1.78      ((![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (sk_A))))
% 1.60/1.78         <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('simplify', [status(thm)], ['52'])).
% 1.60/1.78  thf('54', plain,
% 1.60/1.78      ((![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (sk_A)))
% 1.60/1.78         <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['16', '53'])).
% 1.60/1.78  thf('55', plain,
% 1.60/1.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf('56', plain,
% 1.60/1.78      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (sk_A)))
% 1.60/1.78         <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('demod', [status(thm)], ['54', '55'])).
% 1.60/1.78  thf('57', plain,
% 1.60/1.78      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 1.60/1.78         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['0'])).
% 1.60/1.78  thf('58', plain,
% 1.60/1.78      ((((sk_A) != (k1_xboole_0)))
% 1.60/1.78         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 1.60/1.78             (((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['56', '57'])).
% 1.60/1.78  thf('59', plain,
% 1.60/1.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf('60', plain,
% 1.60/1.78      ((((sk_A) != (sk_A)))
% 1.60/1.78         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 1.60/1.78             (((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('demod', [status(thm)], ['58', '59'])).
% 1.60/1.78  thf('61', plain,
% 1.60/1.78      (~ (((sk_A) = (k1_xboole_0))) | 
% 1.60/1.78       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.60/1.78      inference('simplify', [status(thm)], ['60'])).
% 1.60/1.78  thf('62', plain,
% 1.60/1.78      ((((sk_B) != (k1_xboole_0))
% 1.60/1.78        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('63', plain,
% 1.60/1.78      (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.60/1.78       ~ (((sk_B) = (k1_xboole_0)))),
% 1.60/1.78      inference('split', [status(esa)], ['62'])).
% 1.60/1.78  thf('64', plain,
% 1.60/1.78      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.60/1.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf('65', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 1.60/1.78          | ((X0) = (k1_xboole_0)))),
% 1.60/1.78      inference('demod', [status(thm)], ['44', '45'])).
% 1.60/1.78  thf('66', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 1.60/1.78          | ((X0) = (k1_xboole_0)))),
% 1.60/1.78      inference('demod', [status(thm)], ['44', '45'])).
% 1.60/1.78  thf(l54_zfmisc_1, axiom,
% 1.60/1.78    (![A:$i,B:$i,C:$i,D:$i]:
% 1.60/1.78     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 1.60/1.78       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 1.60/1.78  thf('67', plain,
% 1.60/1.78      (![X22 : $i, X23 : $i, X24 : $i, X26 : $i]:
% 1.60/1.78         ((r2_hidden @ (k4_tarski @ X22 @ X24) @ (k2_zfmisc_1 @ X23 @ X26))
% 1.60/1.78          | ~ (r2_hidden @ X24 @ X26)
% 1.60/1.78          | ~ (r2_hidden @ X22 @ X23))),
% 1.60/1.78      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.60/1.78  thf('68', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.78         (((X0) = (k1_xboole_0))
% 1.60/1.78          | ~ (r2_hidden @ X2 @ X1)
% 1.60/1.78          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_2 @ X0 @ k1_xboole_0)) @ 
% 1.60/1.78             (k2_zfmisc_1 @ X1 @ X0)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['66', '67'])).
% 1.60/1.78  thf('69', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         (((X0) = (k1_xboole_0))
% 1.60/1.78          | (r2_hidden @ 
% 1.60/1.78             (k4_tarski @ (sk_C_2 @ X0 @ k1_xboole_0) @ 
% 1.60/1.78              (sk_C_2 @ X1 @ k1_xboole_0)) @ 
% 1.60/1.78             (k2_zfmisc_1 @ X0 @ X1))
% 1.60/1.78          | ((X1) = (k1_xboole_0)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['65', '68'])).
% 1.60/1.78  thf('70', plain,
% 1.60/1.78      ((((r2_hidden @ 
% 1.60/1.78          (k4_tarski @ (sk_C_2 @ sk_A @ k1_xboole_0) @ 
% 1.60/1.78           (sk_C_2 @ sk_B @ k1_xboole_0)) @ 
% 1.60/1.78          k1_xboole_0)
% 1.60/1.78         | ((sk_B) = (k1_xboole_0))
% 1.60/1.78         | ((sk_A) = (k1_xboole_0))))
% 1.60/1.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup+', [status(thm)], ['64', '69'])).
% 1.60/1.78  thf('71', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.60/1.78      inference('demod', [status(thm)], ['41', '42'])).
% 1.60/1.78  thf('72', plain,
% 1.60/1.78      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 1.60/1.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('clc', [status(thm)], ['70', '71'])).
% 1.60/1.78  thf('73', plain,
% 1.60/1.78      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['62'])).
% 1.60/1.78  thf('74', plain,
% 1.60/1.78      (((((sk_B) != (sk_B)) | ((sk_A) = (k1_xboole_0))))
% 1.60/1.78         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 1.60/1.78             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['72', '73'])).
% 1.60/1.78  thf('75', plain,
% 1.60/1.78      ((((sk_A) = (k1_xboole_0)))
% 1.60/1.78         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 1.60/1.78             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('simplify', [status(thm)], ['74'])).
% 1.60/1.78  thf('76', plain,
% 1.60/1.78      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['0'])).
% 1.60/1.78  thf('77', plain,
% 1.60/1.78      ((((sk_A) != (sk_A)))
% 1.60/1.78         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 1.60/1.78             ~ (((sk_A) = (k1_xboole_0))) & 
% 1.60/1.78             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['75', '76'])).
% 1.60/1.78  thf('78', plain,
% 1.60/1.78      ((((sk_B) = (k1_xboole_0))) | 
% 1.60/1.78       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.60/1.78       (((sk_A) = (k1_xboole_0)))),
% 1.60/1.78      inference('simplify', [status(thm)], ['77'])).
% 1.60/1.78  thf('79', plain, (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.60/1.78      inference('sat_resolution*', [status(thm)], ['2', '61', '63', '78'])).
% 1.60/1.78  thf('80', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 1.60/1.78      inference('simpl_trail', [status(thm)], ['1', '79'])).
% 1.60/1.78  thf('81', plain,
% 1.60/1.78      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf('82', plain,
% 1.60/1.78      ((((sk_B) = (k1_xboole_0))) | 
% 1.60/1.78       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.60/1.78       (((sk_A) = (k1_xboole_0)))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf('83', plain, ((((sk_B) = (k1_xboole_0)))),
% 1.60/1.78      inference('sat_resolution*', [status(thm)], ['2', '61', '63', '78', '82'])).
% 1.60/1.78  thf('84', plain, (((sk_B) = (k1_xboole_0))),
% 1.60/1.78      inference('simpl_trail', [status(thm)], ['81', '83'])).
% 1.60/1.78  thf('85', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (sk_B))),
% 1.60/1.78      inference('demod', [status(thm)], ['80', '84'])).
% 1.60/1.78  thf('86', plain,
% 1.60/1.78      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf('87', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 1.60/1.78      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.60/1.78  thf('88', plain,
% 1.60/1.78      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup+', [status(thm)], ['86', '87'])).
% 1.60/1.78  thf('89', plain, ((((sk_B) = (k1_xboole_0)))),
% 1.60/1.78      inference('sat_resolution*', [status(thm)], ['2', '61', '63', '78', '82'])).
% 1.60/1.78  thf('90', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ sk_B)),
% 1.60/1.78      inference('simpl_trail', [status(thm)], ['88', '89'])).
% 1.60/1.78  thf('91', plain,
% 1.60/1.78      (![X4 : $i, X5 : $i]:
% 1.60/1.78         ((r1_xboole_0 @ X4 @ X5)
% 1.60/1.78          | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 1.60/1.78      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.60/1.78  thf('92', plain,
% 1.60/1.78      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.60/1.78         (~ (r2_hidden @ X27 @ 
% 1.60/1.78             (k3_xboole_0 @ (k2_zfmisc_1 @ X28 @ X29) @ 
% 1.60/1.78              (k2_zfmisc_1 @ X30 @ X31)))
% 1.60/1.78          | (r2_hidden @ (sk_G @ X31 @ X30 @ X29 @ X28 @ X27) @ 
% 1.60/1.78             (k3_xboole_0 @ X29 @ X31)))),
% 1.60/1.78      inference('cnf', [status(esa)], [t104_zfmisc_1])).
% 1.60/1.78  thf('93', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.60/1.78         ((r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0))
% 1.60/1.78          | (r2_hidden @ 
% 1.60/1.78             (sk_G @ X0 @ X1 @ X2 @ X3 @ 
% 1.60/1.78              (sk_C_1 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X3 @ X2))) @ 
% 1.60/1.78             (k3_xboole_0 @ X2 @ X0)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['91', '92'])).
% 1.60/1.78  thf('94', plain,
% 1.60/1.78      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.60/1.78         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 1.60/1.78          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.60/1.78      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.60/1.78  thf('95', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.60/1.78         ((r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ (k2_zfmisc_1 @ X3 @ X0))
% 1.60/1.78          | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['93', '94'])).
% 1.60/1.78  thf('96', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.78         (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ sk_B))),
% 1.60/1.78      inference('sup-', [status(thm)], ['90', '95'])).
% 1.60/1.78  thf('97', plain,
% 1.60/1.78      (![X16 : $i, X20 : $i]:
% 1.60/1.78         (((X20) = (k3_tarski @ X16))
% 1.60/1.78          | (r2_hidden @ (sk_D @ X20 @ X16) @ X16)
% 1.60/1.78          | (r2_hidden @ (sk_C_2 @ X20 @ X16) @ X20))),
% 1.60/1.78      inference('cnf', [status(esa)], [d4_tarski])).
% 1.60/1.78  thf('98', plain,
% 1.60/1.78      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf('99', plain,
% 1.60/1.78      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.60/1.78      inference('cnf', [status(esa)], [t2_boole])).
% 1.60/1.78  thf('100', plain,
% 1.60/1.78      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B) = (k1_xboole_0)))
% 1.60/1.78         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup+', [status(thm)], ['98', '99'])).
% 1.60/1.78  thf('101', plain,
% 1.60/1.78      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf('102', plain,
% 1.60/1.78      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B) = (sk_B)))
% 1.60/1.78         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('demod', [status(thm)], ['100', '101'])).
% 1.60/1.78  thf('103', plain,
% 1.60/1.78      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.60/1.78         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 1.60/1.78          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.60/1.78      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.60/1.78  thf('104', plain,
% 1.60/1.78      ((![X0 : $i, X1 : $i]:
% 1.60/1.78          (~ (r2_hidden @ X1 @ sk_B) | ~ (r1_xboole_0 @ X0 @ sk_B)))
% 1.60/1.78         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['102', '103'])).
% 1.60/1.78  thf('105', plain,
% 1.60/1.78      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup+', [status(thm)], ['86', '87'])).
% 1.60/1.78  thf('106', plain,
% 1.60/1.78      ((![X1 : $i]: ~ (r2_hidden @ X1 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('demod', [status(thm)], ['104', '105'])).
% 1.60/1.78  thf('107', plain,
% 1.60/1.78      ((![X0 : $i]:
% 1.60/1.78          ((r2_hidden @ (sk_C_2 @ X0 @ sk_B) @ X0)
% 1.60/1.78           | ((X0) = (k3_tarski @ sk_B))))
% 1.60/1.78         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['97', '106'])).
% 1.60/1.78  thf('108', plain,
% 1.60/1.78      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf('109', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 1.60/1.78      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 1.60/1.78  thf('110', plain,
% 1.60/1.78      ((((k3_tarski @ sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup+', [status(thm)], ['108', '109'])).
% 1.60/1.78  thf('111', plain,
% 1.60/1.78      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf('112', plain,
% 1.60/1.78      ((((k3_tarski @ sk_B) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('demod', [status(thm)], ['110', '111'])).
% 1.60/1.78  thf('113', plain,
% 1.60/1.78      ((![X0 : $i]: ((r2_hidden @ (sk_C_2 @ X0 @ sk_B) @ X0) | ((X0) = (sk_B))))
% 1.60/1.78         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('demod', [status(thm)], ['107', '112'])).
% 1.60/1.78  thf('114', plain,
% 1.60/1.78      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf('115', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         (((X0) = (k1_xboole_0))
% 1.60/1.78          | ~ (r1_xboole_0 @ X0 @ X1)
% 1.60/1.78          | ~ (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X1))),
% 1.60/1.78      inference('sup-', [status(thm)], ['46', '47'])).
% 1.60/1.78  thf('116', plain,
% 1.60/1.78      ((![X0 : $i, X1 : $i]:
% 1.60/1.78          (~ (r2_hidden @ (sk_C_2 @ X1 @ sk_B) @ X0)
% 1.60/1.78           | ~ (r1_xboole_0 @ X1 @ X0)
% 1.60/1.78           | ((X1) = (k1_xboole_0))))
% 1.60/1.78         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['114', '115'])).
% 1.60/1.78  thf('117', plain,
% 1.60/1.78      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('split', [status(esa)], ['18'])).
% 1.60/1.78  thf('118', plain,
% 1.60/1.78      ((![X0 : $i, X1 : $i]:
% 1.60/1.78          (~ (r2_hidden @ (sk_C_2 @ X1 @ sk_B) @ X0)
% 1.60/1.78           | ~ (r1_xboole_0 @ X1 @ X0)
% 1.60/1.78           | ((X1) = (sk_B))))
% 1.60/1.78         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('demod', [status(thm)], ['116', '117'])).
% 1.60/1.78  thf('119', plain,
% 1.60/1.78      ((![X0 : $i]:
% 1.60/1.78          (((X0) = (sk_B)) | ((X0) = (sk_B)) | ~ (r1_xboole_0 @ X0 @ X0)))
% 1.60/1.78         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['113', '118'])).
% 1.60/1.78  thf('120', plain,
% 1.60/1.78      ((![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (sk_B))))
% 1.60/1.78         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.78      inference('simplify', [status(thm)], ['119'])).
% 1.60/1.78  thf('121', plain, ((((sk_B) = (k1_xboole_0)))),
% 1.60/1.78      inference('sat_resolution*', [status(thm)], ['2', '61', '63', '78', '82'])).
% 1.60/1.78  thf('122', plain,
% 1.60/1.78      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (sk_B)))),
% 1.60/1.78      inference('simpl_trail', [status(thm)], ['120', '121'])).
% 1.60/1.78  thf('123', plain, (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ sk_B) = (sk_B))),
% 1.60/1.78      inference('sup-', [status(thm)], ['96', '122'])).
% 1.60/1.78  thf('124', plain, (((sk_B) != (sk_B))),
% 1.60/1.78      inference('demod', [status(thm)], ['85', '123'])).
% 1.60/1.78  thf('125', plain, ($false), inference('simplify', [status(thm)], ['124'])).
% 1.60/1.78  
% 1.60/1.78  % SZS output end Refutation
% 1.60/1.78  
% 1.62/1.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

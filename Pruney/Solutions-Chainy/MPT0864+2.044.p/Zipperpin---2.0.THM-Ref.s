%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KfbEsVr8gw

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:05 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 750 expanded)
%              Number of leaves         :   29 ( 220 expanded)
%              Depth                    :   21
%              Number of atoms          :  697 (6466 expanded)
%              Number of equality atoms :  106 (1219 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('0',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('1',plain,
    ( ( sk_A_1
      = ( k1_mcart_1 @ sk_A_1 ) )
    | ( sk_A_1
      = ( k2_mcart_1 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( sk_A_1
      = ( k2_mcart_1 @ sk_A_1 ) )
   <= ( sk_A_1
      = ( k2_mcart_1 @ sk_A_1 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( sk_A_1
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( sk_A_1
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('5',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X43 @ X44 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('6',plain,
    ( ( k1_mcart_1 @ sk_A_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( sk_A_1
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,
    ( sk_A_1
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('9',plain,(
    ! [X43: $i,X45: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X43 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('10',plain,
    ( ( k2_mcart_1 @ sk_A_1 )
    = sk_C ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( sk_A_1
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A_1 ) @ ( k2_mcart_1 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,
    ( ( sk_A_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A_1 ) @ sk_A_1 ) )
   <= ( sk_A_1
      = ( k2_mcart_1 @ sk_A_1 ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('14',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X20 = X21 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ ( k2_zfmisc_1 @ X19 @ ( k1_tarski @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ k1_xboole_0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_A_1 @ k1_xboole_0 )
        | ( sk_A_1 = X0 ) )
   <= ( sk_A_1
      = ( k2_mcart_1 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,
    ( ( sk_A_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A_1 ) @ sk_A_1 ) )
   <= ( sk_A_1
      = ( k2_mcart_1 @ sk_A_1 ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X27 ) @ ( k1_tarski @ X28 ) )
      = ( k1_tarski @ ( k4_tarski @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A_1 ) @ ( k1_tarski @ sk_A_1 ) )
      | ( ( k1_tarski @ sk_A_1 )
        = k1_xboole_0 ) )
   <= ( sk_A_1
      = ( k2_mcart_1 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k1_tarski @ sk_A_1 )
      = k1_xboole_0 )
   <= ( sk_A_1
      = ( k2_mcart_1 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t63_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
     => ( r2_hidden @ A @ C ) ) )).

thf('29',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X33 @ X34 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X33 @ X35 ) @ X34 )
       != ( k2_tarski @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t63_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ sk_A_1 @ k1_xboole_0 ) )
   <= ( sk_A_1
      = ( k2_mcart_1 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_A_1 @ k1_xboole_0 )
   <= ( sk_A_1
      = ( k2_mcart_1 @ sk_A_1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('35',plain,
    ( ( sk_A_1
      = ( k1_mcart_1 @ sk_A_1 ) )
   <= ( sk_A_1
      = ( k1_mcart_1 @ sk_A_1 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('36',plain,
    ( sk_A_1
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A_1 ) @ ( k2_mcart_1 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('37',plain,
    ( ( sk_A_1
      = ( k4_tarski @ sk_A_1 @ ( k2_mcart_1 @ sk_A_1 ) ) )
   <= ( sk_A_1
      = ( k1_mcart_1 @ sk_A_1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 = X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X13 ) @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ k1_xboole_0 )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_A_1 @ k1_xboole_0 )
        | ( sk_A_1 = X0 ) )
   <= ( sk_A_1
      = ( k1_mcart_1 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,
    ( ( sk_A_1
      = ( k4_tarski @ sk_A_1 @ ( k2_mcart_1 @ sk_A_1 ) ) )
   <= ( sk_A_1
      = ( k1_mcart_1 @ sk_A_1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('44',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X29 ) @ ( k2_tarski @ X30 @ X31 ) )
      = ( k2_tarski @ ( k4_tarski @ X29 @ X30 ) @ ( k4_tarski @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A_1 ) @ ( k2_tarski @ ( k2_mcart_1 @ sk_A_1 ) @ X0 ) )
        = ( k2_tarski @ sk_A_1 @ ( k4_tarski @ sk_A_1 @ X0 ) ) )
   <= ( sk_A_1
      = ( k1_mcart_1 @ sk_A_1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_A_1
      = ( k4_tarski @ sk_A_1 @ ( k2_mcart_1 @ sk_A_1 ) ) )
   <= ( sk_A_1
      = ( k1_mcart_1 @ sk_A_1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('47',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X27 ) @ ( k1_tarski @ X28 ) )
      = ( k1_tarski @ ( k4_tarski @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('48',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A_1 ) @ ( k1_tarski @ sk_A_1 ) )
      | ( ( k1_tarski @ sk_A_1 )
        = k1_xboole_0 ) )
   <= ( sk_A_1
      = ( k1_mcart_1 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('52',plain,
    ( ( ( k1_tarski @ sk_A_1 )
      = k1_xboole_0 )
   <= ( sk_A_1
      = ( k1_mcart_1 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_tarski @ sk_A_1 @ ( k4_tarski @ sk_A_1 @ X0 ) ) )
   <= ( sk_A_1
      = ( k1_mcart_1 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['45','52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('56',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ sk_A_1 @ k1_xboole_0 ) )
   <= ( sk_A_1
      = ( k1_mcart_1 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r2_hidden @ sk_A_1 @ k1_xboole_0 )
   <= ( sk_A_1
      = ( k1_mcart_1 @ sk_A_1 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ! [X0: $i] : ( sk_A_1 = X0 )
   <= ( sk_A_1
      = ( k1_mcart_1 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['42','57'])).

thf('59',plain,
    ( sk_A_1
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k4_tarski @ A @ B ) ) )).

thf('60',plain,(
    ! [X4: $i,X5: $i] :
      ~ ( v1_xboole_0 @ ( k4_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc1_zfmisc_1])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ~ ( v1_xboole_0 @ X0 )
   <= ( sk_A_1
      = ( k1_mcart_1 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    sk_A_1
 != ( k1_mcart_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['34','62'])).

thf('64',plain,
    ( ( sk_A_1
      = ( k2_mcart_1 @ sk_A_1 ) )
    | ( sk_A_1
      = ( k1_mcart_1 @ sk_A_1 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('65',plain,
    ( sk_A_1
    = ( k2_mcart_1 @ sk_A_1 ) ),
    inference('sat_resolution*',[status(thm)],['63','64'])).

thf('66',plain,(
    r2_hidden @ sk_A_1 @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['33','65'])).

thf('67',plain,
    ( ! [X0: $i] : ( sk_A_1 = X0 )
   <= ( sk_A_1
      = ( k2_mcart_1 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['17','66'])).

thf('68',plain,
    ( sk_A_1
    = ( k2_mcart_1 @ sk_A_1 ) ),
    inference('sat_resolution*',[status(thm)],['63','64'])).

thf('69',plain,(
    ! [X0: $i] : ( sk_A_1 = X0 ) ),
    inference(simpl_trail,[status(thm)],['67','68'])).

thf('70',plain,(
    v1_xboole_0 @ sk_A_1 ),
    inference(demod,[status(thm)],['0','69'])).

thf('71',plain,(
    ! [X0: $i] : ( sk_A_1 = X0 ) ),
    inference(simpl_trail,[status(thm)],['67','68'])).

thf('72',plain,(
    ~ ( v1_xboole_0 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('73',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference('sup-',[status(thm)],['70','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KfbEsVr8gw
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:29:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 346 iterations in 0.175s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.45/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.67  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.45/0.67  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.45/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.67  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.45/0.67  thf('0', plain, ((v1_xboole_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.45/0.67  thf(t20_mcart_1, conjecture,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.45/0.67       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i]:
% 0.45/0.67        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.45/0.67          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      ((((sk_A_1) = (k1_mcart_1 @ sk_A_1)) | ((sk_A_1) = (k2_mcart_1 @ sk_A_1)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      ((((sk_A_1) = (k2_mcart_1 @ sk_A_1)))
% 0.45/0.67         <= ((((sk_A_1) = (k2_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('split', [status(esa)], ['1'])).
% 0.45/0.67  thf('3', plain, (((sk_A_1) = (k4_tarski @ sk_B @ sk_C))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('4', plain, (((sk_A_1) = (k4_tarski @ sk_B @ sk_C))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(t7_mcart_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.45/0.67       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      (![X43 : $i, X44 : $i]: ((k1_mcart_1 @ (k4_tarski @ X43 @ X44)) = (X43))),
% 0.45/0.67      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.45/0.67  thf('6', plain, (((k1_mcart_1 @ sk_A_1) = (sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.67  thf('7', plain, (((sk_A_1) = (k4_tarski @ (k1_mcart_1 @ sk_A_1) @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['3', '6'])).
% 0.45/0.67  thf('8', plain, (((sk_A_1) = (k4_tarski @ (k1_mcart_1 @ sk_A_1) @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['3', '6'])).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (![X43 : $i, X45 : $i]: ((k2_mcart_1 @ (k4_tarski @ X43 @ X45)) = (X45))),
% 0.45/0.67      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.45/0.67  thf('10', plain, (((k2_mcart_1 @ sk_A_1) = (sk_C))),
% 0.45/0.67      inference('sup+', [status(thm)], ['8', '9'])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      (((sk_A_1) = (k4_tarski @ (k1_mcart_1 @ sk_A_1) @ (k2_mcart_1 @ sk_A_1)))),
% 0.45/0.67      inference('demod', [status(thm)], ['7', '10'])).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      ((((sk_A_1) = (k4_tarski @ (k1_mcart_1 @ sk_A_1) @ sk_A_1)))
% 0.45/0.67         <= ((((sk_A_1) = (k2_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['2', '11'])).
% 0.45/0.67  thf(t113_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.67       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (![X11 : $i, X12 : $i]:
% 0.45/0.67         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.45/0.67          | ((X11) != (k1_xboole_0)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.45/0.67  thf('14', plain,
% 0.45/0.67      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['13'])).
% 0.45/0.67  thf(t129_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( r2_hidden @
% 0.45/0.67         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.45/0.67       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.67         (((X20) = (X21))
% 0.45/0.67          | ~ (r2_hidden @ (k4_tarski @ X18 @ X20) @ 
% 0.45/0.67               (k2_zfmisc_1 @ X19 @ (k1_tarski @ X21))))),
% 0.45/0.67      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ k1_xboole_0) | ((X1) = (X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      ((![X0 : $i]: (~ (r2_hidden @ sk_A_1 @ k1_xboole_0) | ((sk_A_1) = (X0))))
% 0.45/0.67         <= ((((sk_A_1) = (k2_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['12', '16'])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      ((((sk_A_1) = (k4_tarski @ (k1_mcart_1 @ sk_A_1) @ sk_A_1)))
% 0.45/0.67         <= ((((sk_A_1) = (k2_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['2', '11'])).
% 0.45/0.67  thf(t35_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.45/0.67       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      (![X27 : $i, X28 : $i]:
% 0.45/0.67         ((k2_zfmisc_1 @ (k1_tarski @ X27) @ (k1_tarski @ X28))
% 0.45/0.67           = (k1_tarski @ (k4_tarski @ X27 @ X28)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.45/0.67  thf(t135_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.45/0.67         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.45/0.67       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (![X25 : $i, X26 : $i]:
% 0.45/0.67         (((X25) = (k1_xboole_0))
% 0.45/0.67          | ~ (r1_tarski @ X25 @ (k2_zfmisc_1 @ X26 @ X25)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.45/0.67  thf('21', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.45/0.67          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      (((~ (r1_tarski @ (k1_tarski @ sk_A_1) @ (k1_tarski @ sk_A_1))
% 0.45/0.67         | ((k1_tarski @ sk_A_1) = (k1_xboole_0))))
% 0.45/0.67         <= ((((sk_A_1) = (k2_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['18', '21'])).
% 0.45/0.67  thf(t69_enumset1, axiom,
% 0.45/0.67    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.67  thf('23', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.45/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.67  thf(t12_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      (![X23 : $i, X24 : $i]:
% 0.45/0.67         (r1_tarski @ (k1_tarski @ X23) @ (k2_tarski @ X23 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['23', '24'])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      ((((k1_tarski @ sk_A_1) = (k1_xboole_0)))
% 0.45/0.67         <= ((((sk_A_1) = (k2_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('demod', [status(thm)], ['22', '25'])).
% 0.45/0.67  thf('27', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.45/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.67  thf(t2_boole, axiom,
% 0.45/0.67    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.67  thf('28', plain,
% 0.45/0.67      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.67      inference('cnf', [status(esa)], [t2_boole])).
% 0.45/0.67  thf(t63_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.45/0.67       ( r2_hidden @ A @ C ) ))).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.45/0.67         ((r2_hidden @ X33 @ X34)
% 0.45/0.67          | ((k3_xboole_0 @ (k2_tarski @ X33 @ X35) @ X34)
% 0.45/0.67              != (k2_tarski @ X33 @ X35)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t63_zfmisc_1])).
% 0.45/0.67  thf('30', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((k1_xboole_0) != (k2_tarski @ X1 @ X0))
% 0.45/0.67          | (r2_hidden @ X1 @ k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.67  thf('31', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (((k1_xboole_0) != (k1_tarski @ X0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['27', '30'])).
% 0.45/0.67  thf('32', plain,
% 0.45/0.67      (((((k1_xboole_0) != (k1_xboole_0)) | (r2_hidden @ sk_A_1 @ k1_xboole_0)))
% 0.45/0.67         <= ((((sk_A_1) = (k2_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['26', '31'])).
% 0.45/0.67  thf('33', plain,
% 0.45/0.67      (((r2_hidden @ sk_A_1 @ k1_xboole_0))
% 0.45/0.67         <= ((((sk_A_1) = (k2_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('simplify', [status(thm)], ['32'])).
% 0.45/0.67  thf('34', plain, ((v1_xboole_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      ((((sk_A_1) = (k1_mcart_1 @ sk_A_1)))
% 0.45/0.67         <= ((((sk_A_1) = (k1_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('split', [status(esa)], ['1'])).
% 0.45/0.67  thf('36', plain,
% 0.45/0.67      (((sk_A_1) = (k4_tarski @ (k1_mcart_1 @ sk_A_1) @ (k2_mcart_1 @ sk_A_1)))),
% 0.45/0.67      inference('demod', [status(thm)], ['7', '10'])).
% 0.45/0.67  thf('37', plain,
% 0.45/0.67      ((((sk_A_1) = (k4_tarski @ sk_A_1 @ (k2_mcart_1 @ sk_A_1))))
% 0.45/0.67         <= ((((sk_A_1) = (k1_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['35', '36'])).
% 0.45/0.67  thf('38', plain,
% 0.45/0.67      (![X11 : $i, X12 : $i]:
% 0.45/0.67         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.45/0.67          | ((X12) != (k1_xboole_0)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.45/0.67  thf('39', plain,
% 0.45/0.67      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['38'])).
% 0.45/0.67  thf(t128_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( r2_hidden @
% 0.45/0.67         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.45/0.67       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.45/0.67  thf('40', plain,
% 0.45/0.67      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.67         (((X14) = (X13))
% 0.45/0.67          | ~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ 
% 0.45/0.67               (k2_zfmisc_1 @ (k1_tarski @ X13) @ X16)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.45/0.67  thf('41', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ k1_xboole_0) | ((X2) = (X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.67  thf('42', plain,
% 0.45/0.67      ((![X0 : $i]: (~ (r2_hidden @ sk_A_1 @ k1_xboole_0) | ((sk_A_1) = (X0))))
% 0.45/0.67         <= ((((sk_A_1) = (k1_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['37', '41'])).
% 0.45/0.67  thf('43', plain,
% 0.45/0.67      ((((sk_A_1) = (k4_tarski @ sk_A_1 @ (k2_mcart_1 @ sk_A_1))))
% 0.45/0.67         <= ((((sk_A_1) = (k1_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['35', '36'])).
% 0.45/0.67  thf(t36_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.45/0.67         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.45/0.67       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.45/0.67         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.45/0.67  thf('44', plain,
% 0.45/0.67      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.45/0.67         ((k2_zfmisc_1 @ (k1_tarski @ X29) @ (k2_tarski @ X30 @ X31))
% 0.45/0.67           = (k2_tarski @ (k4_tarski @ X29 @ X30) @ (k4_tarski @ X29 @ X31)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.45/0.67  thf('45', plain,
% 0.45/0.67      ((![X0 : $i]:
% 0.45/0.67          ((k2_zfmisc_1 @ (k1_tarski @ sk_A_1) @ 
% 0.45/0.67            (k2_tarski @ (k2_mcart_1 @ sk_A_1) @ X0))
% 0.45/0.67            = (k2_tarski @ sk_A_1 @ (k4_tarski @ sk_A_1 @ X0))))
% 0.45/0.67         <= ((((sk_A_1) = (k1_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['43', '44'])).
% 0.45/0.67  thf('46', plain,
% 0.45/0.67      ((((sk_A_1) = (k4_tarski @ sk_A_1 @ (k2_mcart_1 @ sk_A_1))))
% 0.45/0.67         <= ((((sk_A_1) = (k1_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['35', '36'])).
% 0.45/0.67  thf('47', plain,
% 0.45/0.67      (![X27 : $i, X28 : $i]:
% 0.45/0.67         ((k2_zfmisc_1 @ (k1_tarski @ X27) @ (k1_tarski @ X28))
% 0.45/0.67           = (k1_tarski @ (k4_tarski @ X27 @ X28)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.45/0.67  thf('48', plain,
% 0.45/0.67      (![X25 : $i, X26 : $i]:
% 0.45/0.67         (((X25) = (k1_xboole_0))
% 0.45/0.67          | ~ (r1_tarski @ X25 @ (k2_zfmisc_1 @ X25 @ X26)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.45/0.67  thf('49', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.45/0.67          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.67  thf('50', plain,
% 0.45/0.67      (((~ (r1_tarski @ (k1_tarski @ sk_A_1) @ (k1_tarski @ sk_A_1))
% 0.45/0.67         | ((k1_tarski @ sk_A_1) = (k1_xboole_0))))
% 0.45/0.67         <= ((((sk_A_1) = (k1_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['46', '49'])).
% 0.45/0.67  thf('51', plain,
% 0.45/0.67      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['23', '24'])).
% 0.45/0.67  thf('52', plain,
% 0.45/0.67      ((((k1_tarski @ sk_A_1) = (k1_xboole_0)))
% 0.45/0.67         <= ((((sk_A_1) = (k1_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.67  thf('53', plain,
% 0.45/0.67      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['13'])).
% 0.45/0.67  thf('54', plain,
% 0.45/0.67      ((![X0 : $i]:
% 0.45/0.67          ((k1_xboole_0) = (k2_tarski @ sk_A_1 @ (k4_tarski @ sk_A_1 @ X0))))
% 0.45/0.67         <= ((((sk_A_1) = (k1_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('demod', [status(thm)], ['45', '52', '53'])).
% 0.45/0.67  thf('55', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((k1_xboole_0) != (k2_tarski @ X1 @ X0))
% 0.45/0.67          | (r2_hidden @ X1 @ k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.67  thf('56', plain,
% 0.45/0.67      (((((k1_xboole_0) != (k1_xboole_0)) | (r2_hidden @ sk_A_1 @ k1_xboole_0)))
% 0.45/0.67         <= ((((sk_A_1) = (k1_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['54', '55'])).
% 0.45/0.67  thf('57', plain,
% 0.45/0.67      (((r2_hidden @ sk_A_1 @ k1_xboole_0))
% 0.45/0.67         <= ((((sk_A_1) = (k1_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('simplify', [status(thm)], ['56'])).
% 0.45/0.67  thf('58', plain,
% 0.45/0.67      ((![X0 : $i]: ((sk_A_1) = (X0)))
% 0.45/0.67         <= ((((sk_A_1) = (k1_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('demod', [status(thm)], ['42', '57'])).
% 0.45/0.67  thf('59', plain, (((sk_A_1) = (k4_tarski @ sk_B @ sk_C))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(fc1_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k4_tarski @ A @ B ) ) ))).
% 0.45/0.67  thf('60', plain,
% 0.45/0.67      (![X4 : $i, X5 : $i]: ~ (v1_xboole_0 @ (k4_tarski @ X4 @ X5))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc1_zfmisc_1])).
% 0.45/0.67  thf('61', plain, (~ (v1_xboole_0 @ sk_A_1)),
% 0.45/0.67      inference('sup-', [status(thm)], ['59', '60'])).
% 0.45/0.67  thf('62', plain,
% 0.45/0.67      ((![X0 : $i]: ~ (v1_xboole_0 @ X0))
% 0.45/0.67         <= ((((sk_A_1) = (k1_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['58', '61'])).
% 0.45/0.67  thf('63', plain, (~ (((sk_A_1) = (k1_mcart_1 @ sk_A_1)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['34', '62'])).
% 0.45/0.67  thf('64', plain,
% 0.45/0.67      ((((sk_A_1) = (k2_mcart_1 @ sk_A_1))) | 
% 0.45/0.67       (((sk_A_1) = (k1_mcart_1 @ sk_A_1)))),
% 0.45/0.67      inference('split', [status(esa)], ['1'])).
% 0.45/0.67  thf('65', plain, ((((sk_A_1) = (k2_mcart_1 @ sk_A_1)))),
% 0.45/0.67      inference('sat_resolution*', [status(thm)], ['63', '64'])).
% 0.45/0.67  thf('66', plain, ((r2_hidden @ sk_A_1 @ k1_xboole_0)),
% 0.45/0.67      inference('simpl_trail', [status(thm)], ['33', '65'])).
% 0.45/0.67  thf('67', plain,
% 0.45/0.67      ((![X0 : $i]: ((sk_A_1) = (X0)))
% 0.45/0.67         <= ((((sk_A_1) = (k2_mcart_1 @ sk_A_1))))),
% 0.45/0.67      inference('demod', [status(thm)], ['17', '66'])).
% 0.45/0.67  thf('68', plain, ((((sk_A_1) = (k2_mcart_1 @ sk_A_1)))),
% 0.45/0.67      inference('sat_resolution*', [status(thm)], ['63', '64'])).
% 0.45/0.67  thf('69', plain, (![X0 : $i]: ((sk_A_1) = (X0))),
% 0.45/0.67      inference('simpl_trail', [status(thm)], ['67', '68'])).
% 0.45/0.67  thf('70', plain, ((v1_xboole_0 @ sk_A_1)),
% 0.45/0.67      inference('demod', [status(thm)], ['0', '69'])).
% 0.45/0.67  thf('71', plain, (![X0 : $i]: ((sk_A_1) = (X0))),
% 0.45/0.67      inference('simpl_trail', [status(thm)], ['67', '68'])).
% 0.45/0.67  thf('72', plain, (~ (v1_xboole_0 @ sk_A_1)),
% 0.45/0.67      inference('sup-', [status(thm)], ['59', '60'])).
% 0.45/0.67  thf('73', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.45/0.67      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.67  thf('74', plain, ($false), inference('sup-', [status(thm)], ['70', '73'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

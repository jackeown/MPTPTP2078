%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I20AmzX4BI

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:04 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 350 expanded)
%              Number of leaves         :   22 ( 107 expanded)
%              Depth                    :   16
%              Number of atoms          : 1191 (3870 expanded)
%              Number of equality atoms :  153 ( 343 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( ( r1_xboole_0 @ X5 @ X5 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('5',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('8',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i,X20: $i] :
      ( ( X20
        = ( k2_zfmisc_1 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X20 @ X16 @ X17 ) @ ( sk_E @ X20 @ X16 @ X17 ) @ ( sk_D @ X20 @ X16 @ X17 ) @ X16 @ X17 )
      | ( r2_hidden @ ( sk_D @ X20 @ X16 @ X17 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ X10 )
      | ~ ( zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('32',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('38',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','41'])).

thf('43',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( sk_B_1
        = ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('49',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['45'])).

thf('52',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('53',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('54',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('55',plain,(
    ! [X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X23 @ X25 ) @ ( k2_zfmisc_1 @ X24 @ X27 ) )
      | ~ ( r2_hidden @ X25 @ X27 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('60',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_B @ X1 ) @ ( sk_B @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('65',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['45'])).

thf('71',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('74',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf('75',plain,
    ( ( r1_xboole_0 @ sk_A @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('77',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_A @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('83',plain,(
    ! [X16: $i,X17: $i,X20: $i] :
      ( ( X20
        = ( k2_zfmisc_1 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X20 @ X16 @ X17 ) @ ( sk_E @ X20 @ X16 @ X17 ) @ ( sk_D @ X20 @ X16 @ X17 ) @ X16 @ X17 )
      | ( r2_hidden @ ( sk_D @ X20 @ X16 @ X17 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('84',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X7 @ X11 )
      | ~ ( zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('87',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['82','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['82','90'])).

thf('93',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','96'])).

thf('98',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['45'])).

thf('101',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('103',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('106',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','50','51','72','104','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I20AmzX4BI
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.94  % Solved by: fo/fo7.sh
% 0.76/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.94  % done 520 iterations in 0.477s
% 0.76/0.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.94  % SZS output start Refutation
% 0.76/0.94  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.76/0.94  thf(sk_B_type, type, sk_B: $i > $i).
% 0.76/0.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.94  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.76/0.94  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.76/0.94  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.76/0.94  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.76/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.94  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.76/0.94  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.76/0.94  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.76/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.94  thf(t113_zfmisc_1, conjecture,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.76/0.94       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.76/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.94    (~( ![A:$i,B:$i]:
% 0.76/0.94        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.76/0.94          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.76/0.94    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.76/0.94  thf('0', plain,
% 0.76/0.94      ((((sk_B_1) != (k1_xboole_0))
% 0.76/0.94        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('1', plain,
% 0.76/0.94      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.76/0.94       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.76/0.94      inference('split', [status(esa)], ['0'])).
% 0.76/0.94  thf('2', plain,
% 0.76/0.94      ((((sk_B_1) = (k1_xboole_0))
% 0.76/0.94        | ((sk_A) = (k1_xboole_0))
% 0.76/0.94        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('3', plain,
% 0.76/0.94      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('split', [status(esa)], ['2'])).
% 0.76/0.94  thf(t66_xboole_1, axiom,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.76/0.94       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.76/0.94  thf('4', plain,
% 0.76/0.94      (![X5 : $i]: ((r1_xboole_0 @ X5 @ X5) | ((X5) != (k1_xboole_0)))),
% 0.76/0.94      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.76/0.94  thf('5', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.76/0.94      inference('simplify', [status(thm)], ['4'])).
% 0.76/0.94  thf('6', plain,
% 0.76/0.94      (((r1_xboole_0 @ sk_B_1 @ k1_xboole_0)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('sup+', [status(thm)], ['3', '5'])).
% 0.76/0.94  thf('7', plain,
% 0.76/0.94      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('split', [status(esa)], ['2'])).
% 0.76/0.94  thf('8', plain,
% 0.76/0.94      (((r1_xboole_0 @ sk_B_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('demod', [status(thm)], ['6', '7'])).
% 0.76/0.94  thf(t3_xboole_0, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.76/0.94            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.76/0.94       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.76/0.94            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.76/0.94  thf('9', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.76/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/0.94  thf('10', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.76/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/0.94  thf('11', plain,
% 0.76/0.94      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.76/0.94         (~ (r2_hidden @ X2 @ X0)
% 0.76/0.94          | ~ (r2_hidden @ X2 @ X3)
% 0.76/0.94          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.76/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/0.94  thf('12', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         ((r1_xboole_0 @ X0 @ X1)
% 0.76/0.94          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.76/0.94          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.76/0.94      inference('sup-', [status(thm)], ['10', '11'])).
% 0.76/0.94  thf('13', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((r1_xboole_0 @ X0 @ X1)
% 0.76/0.94          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.76/0.94          | (r1_xboole_0 @ X0 @ X1))),
% 0.76/0.94      inference('sup-', [status(thm)], ['9', '12'])).
% 0.76/0.94  thf('14', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.76/0.94      inference('simplify', [status(thm)], ['13'])).
% 0.76/0.94  thf('15', plain,
% 0.76/0.94      ((![X0 : $i]: (r1_xboole_0 @ sk_B_1 @ X0))
% 0.76/0.94         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['8', '14'])).
% 0.76/0.94  thf('16', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.76/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/0.94  thf('17', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.76/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/0.94  thf('18', plain,
% 0.76/0.94      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.76/0.94         (~ (r2_hidden @ X2 @ X0)
% 0.76/0.94          | ~ (r2_hidden @ X2 @ X3)
% 0.76/0.94          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.76/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/0.94  thf('19', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         ((r1_xboole_0 @ X1 @ X0)
% 0.76/0.94          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.76/0.94          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.76/0.94      inference('sup-', [status(thm)], ['17', '18'])).
% 0.76/0.94  thf('20', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((r1_xboole_0 @ X0 @ X1)
% 0.76/0.94          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.76/0.94          | (r1_xboole_0 @ X0 @ X1))),
% 0.76/0.94      inference('sup-', [status(thm)], ['16', '19'])).
% 0.76/0.94  thf('21', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.76/0.94      inference('simplify', [status(thm)], ['20'])).
% 0.76/0.94  thf('22', plain,
% 0.76/0.94      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_B_1))
% 0.76/0.94         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['15', '21'])).
% 0.76/0.94  thf('23', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.76/0.94      inference('simplify', [status(thm)], ['4'])).
% 0.76/0.94  thf('24', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.76/0.94      inference('simplify', [status(thm)], ['13'])).
% 0.76/0.94  thf('25', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.76/0.94      inference('sup-', [status(thm)], ['23', '24'])).
% 0.76/0.94  thf('26', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.76/0.94      inference('simplify', [status(thm)], ['20'])).
% 0.76/0.94  thf('27', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.76/0.94      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.94  thf(d2_zfmisc_1, axiom,
% 0.76/0.94    (![A:$i,B:$i,C:$i]:
% 0.76/0.94     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.76/0.94       ( ![D:$i]:
% 0.76/0.94         ( ( r2_hidden @ D @ C ) <=>
% 0.76/0.94           ( ?[E:$i,F:$i]:
% 0.76/0.94             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.76/0.94               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.76/0.94  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.76/0.94  thf(zf_stmt_2, axiom,
% 0.76/0.94    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.76/0.94     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.76/0.94       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.76/0.94         ( r2_hidden @ E @ A ) ) ))).
% 0.76/0.94  thf(zf_stmt_3, axiom,
% 0.76/0.94    (![A:$i,B:$i,C:$i]:
% 0.76/0.94     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.76/0.94       ( ![D:$i]:
% 0.76/0.94         ( ( r2_hidden @ D @ C ) <=>
% 0.76/0.94           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.76/0.94  thf('28', plain,
% 0.76/0.94      (![X16 : $i, X17 : $i, X20 : $i]:
% 0.76/0.94         (((X20) = (k2_zfmisc_1 @ X17 @ X16))
% 0.76/0.94          | (zip_tseitin_0 @ (sk_F @ X20 @ X16 @ X17) @ 
% 0.76/0.94             (sk_E @ X20 @ X16 @ X17) @ (sk_D @ X20 @ X16 @ X17) @ X16 @ X17)
% 0.76/0.94          | (r2_hidden @ (sk_D @ X20 @ X16 @ X17) @ X20))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.76/0.94  thf('29', plain,
% 0.76/0.94      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.76/0.94         ((r2_hidden @ X8 @ X10) | ~ (zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/0.94  thf('30', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.76/0.94          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.76/0.94          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.76/0.94      inference('sup-', [status(thm)], ['28', '29'])).
% 0.76/0.94  thf('31', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.76/0.94          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.76/0.94          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.76/0.94      inference('sup-', [status(thm)], ['28', '29'])).
% 0.76/0.94  thf('32', plain,
% 0.76/0.94      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.76/0.94         (~ (r2_hidden @ X2 @ X0)
% 0.76/0.94          | ~ (r2_hidden @ X2 @ X3)
% 0.76/0.94          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.76/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/0.94  thf('33', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.94         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 0.76/0.94          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.76/0.94          | ~ (r1_xboole_0 @ X0 @ X3)
% 0.76/0.94          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X3))),
% 0.76/0.94      inference('sup-', [status(thm)], ['31', '32'])).
% 0.76/0.94  thf('34', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 0.76/0.94          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.76/0.94          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.76/0.94          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.76/0.94          | (r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2))),
% 0.76/0.94      inference('sup-', [status(thm)], ['30', '33'])).
% 0.76/0.94  thf('35', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         (~ (r1_xboole_0 @ X0 @ X0)
% 0.76/0.94          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.76/0.94          | (r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2))),
% 0.76/0.94      inference('simplify', [status(thm)], ['34'])).
% 0.76/0.94  thf('36', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X0)
% 0.76/0.94          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['27', '35'])).
% 0.76/0.94  thf('37', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X0)
% 0.76/0.94          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['27', '35'])).
% 0.76/0.94  thf('38', plain,
% 0.76/0.94      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.76/0.94         (~ (r2_hidden @ X2 @ X0)
% 0.76/0.94          | ~ (r2_hidden @ X2 @ X3)
% 0.76/0.94          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.76/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/0.94  thf('39', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         (((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0))
% 0.76/0.94          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.76/0.94          | ~ (r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X2))),
% 0.76/0.94      inference('sup-', [status(thm)], ['37', '38'])).
% 0.76/0.94  thf('40', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0))
% 0.76/0.94          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.76/0.94          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['36', '39'])).
% 0.76/0.94  thf('41', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (~ (r1_xboole_0 @ X0 @ X0) | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.76/0.94      inference('simplify', [status(thm)], ['40'])).
% 0.76/0.94  thf('42', plain,
% 0.76/0.94      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.76/0.94         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['22', '41'])).
% 0.76/0.94  thf('43', plain,
% 0.76/0.94      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('split', [status(esa)], ['2'])).
% 0.76/0.94  thf('44', plain,
% 0.76/0.94      ((![X0 : $i]: ((sk_B_1) = (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.76/0.94         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('demod', [status(thm)], ['42', '43'])).
% 0.76/0.94  thf('45', plain,
% 0.76/0.94      ((((sk_A) != (k1_xboole_0))
% 0.76/0.94        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('46', plain,
% 0.76/0.94      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.76/0.94         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('split', [status(esa)], ['45'])).
% 0.76/0.94  thf('47', plain,
% 0.76/0.94      ((((sk_B_1) != (k1_xboole_0)))
% 0.76/0.94         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.76/0.94             (((sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['44', '46'])).
% 0.76/0.94  thf('48', plain,
% 0.76/0.94      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('split', [status(esa)], ['2'])).
% 0.76/0.94  thf('49', plain,
% 0.76/0.94      ((((sk_B_1) != (sk_B_1)))
% 0.76/0.94         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.76/0.94             (((sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('demod', [status(thm)], ['47', '48'])).
% 0.76/0.94  thf('50', plain,
% 0.76/0.94      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.76/0.94       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.76/0.94      inference('simplify', [status(thm)], ['49'])).
% 0.76/0.94  thf('51', plain,
% 0.76/0.94      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.76/0.94       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.76/0.94      inference('split', [status(esa)], ['45'])).
% 0.76/0.94  thf('52', plain,
% 0.76/0.94      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.76/0.94         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('split', [status(esa)], ['2'])).
% 0.76/0.94  thf(t7_xboole_0, axiom,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.76/0.94          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.76/0.94  thf('53', plain,
% 0.76/0.94      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.76/0.94      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.76/0.94  thf('54', plain,
% 0.76/0.94      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.76/0.94      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.76/0.94  thf(l54_zfmisc_1, axiom,
% 0.76/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.94     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.76/0.94       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.76/0.94  thf('55', plain,
% 0.76/0.94      (![X23 : $i, X24 : $i, X25 : $i, X27 : $i]:
% 0.76/0.94         ((r2_hidden @ (k4_tarski @ X23 @ X25) @ (k2_zfmisc_1 @ X24 @ X27))
% 0.76/0.94          | ~ (r2_hidden @ X25 @ X27)
% 0.76/0.94          | ~ (r2_hidden @ X23 @ X24))),
% 0.76/0.94      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.76/0.94  thf('56', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         (((X0) = (k1_xboole_0))
% 0.76/0.94          | ~ (r2_hidden @ X2 @ X1)
% 0.76/0.94          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.76/0.94             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['54', '55'])).
% 0.76/0.94  thf('57', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (((X0) = (k1_xboole_0))
% 0.76/0.94          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 0.76/0.94             (k2_zfmisc_1 @ X0 @ X1))
% 0.76/0.94          | ((X1) = (k1_xboole_0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['53', '56'])).
% 0.76/0.94  thf('58', plain,
% 0.76/0.94      ((((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.76/0.94          k1_xboole_0)
% 0.76/0.94         | ((sk_B_1) = (k1_xboole_0))
% 0.76/0.94         | ((sk_A) = (k1_xboole_0))))
% 0.76/0.94         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('sup+', [status(thm)], ['52', '57'])).
% 0.76/0.94  thf('59', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (((X0) = (k1_xboole_0))
% 0.76/0.94          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 0.76/0.94             (k2_zfmisc_1 @ X0 @ X1))
% 0.76/0.94          | ((X1) = (k1_xboole_0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['53', '56'])).
% 0.76/0.94  thf('60', plain,
% 0.76/0.94      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.76/0.94         (~ (r2_hidden @ X2 @ X0)
% 0.76/0.94          | ~ (r2_hidden @ X2 @ X3)
% 0.76/0.94          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.76/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/0.94  thf('61', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         (((X0) = (k1_xboole_0))
% 0.76/0.94          | ((X1) = (k1_xboole_0))
% 0.76/0.94          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ X2)
% 0.76/0.94          | ~ (r2_hidden @ (k4_tarski @ (sk_B @ X1) @ (sk_B @ X0)) @ X2))),
% 0.76/0.94      inference('sup-', [status(thm)], ['59', '60'])).
% 0.76/0.94  thf('62', plain,
% 0.76/0.94      (((((sk_A) = (k1_xboole_0))
% 0.76/0.94         | ((sk_B_1) = (k1_xboole_0))
% 0.76/0.94         | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ k1_xboole_0)
% 0.76/0.94         | ((sk_A) = (k1_xboole_0))
% 0.76/0.94         | ((sk_B_1) = (k1_xboole_0))))
% 0.76/0.94         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['58', '61'])).
% 0.76/0.94  thf('63', plain,
% 0.76/0.94      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.76/0.94         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('split', [status(esa)], ['2'])).
% 0.76/0.94  thf('64', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.76/0.94      inference('sup-', [status(thm)], ['23', '24'])).
% 0.76/0.94  thf('65', plain,
% 0.76/0.94      (((((sk_A) = (k1_xboole_0))
% 0.76/0.94         | ((sk_B_1) = (k1_xboole_0))
% 0.76/0.94         | ((sk_A) = (k1_xboole_0))
% 0.76/0.94         | ((sk_B_1) = (k1_xboole_0))))
% 0.76/0.94         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.76/0.94  thf('66', plain,
% 0.76/0.94      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.76/0.94         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('simplify', [status(thm)], ['65'])).
% 0.76/0.94  thf('67', plain,
% 0.76/0.94      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('split', [status(esa)], ['0'])).
% 0.76/0.94  thf('68', plain,
% 0.76/0.94      (((((sk_B_1) != (sk_B_1)) | ((sk_A) = (k1_xboole_0))))
% 0.76/0.94         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.76/0.94             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['66', '67'])).
% 0.76/0.94  thf('69', plain,
% 0.76/0.94      ((((sk_A) = (k1_xboole_0)))
% 0.76/0.94         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.76/0.94             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('simplify', [status(thm)], ['68'])).
% 0.76/0.94  thf('70', plain,
% 0.76/0.94      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.76/0.94      inference('split', [status(esa)], ['45'])).
% 0.76/0.94  thf('71', plain,
% 0.76/0.94      ((((sk_A) != (sk_A)))
% 0.76/0.94         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.76/0.94             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.76/0.94             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['69', '70'])).
% 0.76/0.94  thf('72', plain,
% 0.76/0.94      ((((sk_A) = (k1_xboole_0))) | 
% 0.76/0.94       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.76/0.94       (((sk_B_1) = (k1_xboole_0)))),
% 0.76/0.94      inference('simplify', [status(thm)], ['71'])).
% 0.76/0.94  thf('73', plain,
% 0.76/0.94      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.94      inference('split', [status(esa)], ['2'])).
% 0.76/0.94  thf('74', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.76/0.94      inference('simplify', [status(thm)], ['4'])).
% 0.76/0.94  thf('75', plain,
% 0.76/0.94      (((r1_xboole_0 @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.94      inference('sup+', [status(thm)], ['73', '74'])).
% 0.76/0.94  thf('76', plain,
% 0.76/0.94      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.94      inference('split', [status(esa)], ['2'])).
% 0.76/0.94  thf('77', plain,
% 0.76/0.94      (((r1_xboole_0 @ sk_A @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.94      inference('demod', [status(thm)], ['75', '76'])).
% 0.76/0.94  thf('78', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.76/0.94      inference('simplify', [status(thm)], ['13'])).
% 0.76/0.94  thf('79', plain,
% 0.76/0.94      ((![X0 : $i]: (r1_xboole_0 @ sk_A @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['77', '78'])).
% 0.76/0.94  thf('80', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.76/0.94      inference('simplify', [status(thm)], ['20'])).
% 0.76/0.94  thf('81', plain,
% 0.76/0.94      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['79', '80'])).
% 0.76/0.94  thf('82', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.76/0.94      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.94  thf('83', plain,
% 0.76/0.94      (![X16 : $i, X17 : $i, X20 : $i]:
% 0.76/0.94         (((X20) = (k2_zfmisc_1 @ X17 @ X16))
% 0.76/0.94          | (zip_tseitin_0 @ (sk_F @ X20 @ X16 @ X17) @ 
% 0.76/0.94             (sk_E @ X20 @ X16 @ X17) @ (sk_D @ X20 @ X16 @ X17) @ X16 @ X17)
% 0.76/0.94          | (r2_hidden @ (sk_D @ X20 @ X16 @ X17) @ X20))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.76/0.94  thf('84', plain,
% 0.76/0.94      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.76/0.94         ((r2_hidden @ X7 @ X11) | ~ (zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/0.94  thf('85', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.76/0.94          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.76/0.94          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['83', '84'])).
% 0.76/0.94  thf('86', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.76/0.94          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.76/0.94          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['83', '84'])).
% 0.76/0.94  thf('87', plain,
% 0.76/0.94      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.76/0.94         (~ (r2_hidden @ X2 @ X0)
% 0.76/0.94          | ~ (r2_hidden @ X2 @ X3)
% 0.76/0.94          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.76/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/0.94  thf('88', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.94         ((r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1)
% 0.76/0.94          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.76/0.94          | ~ (r1_xboole_0 @ X0 @ X3)
% 0.76/0.94          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X3))),
% 0.76/0.94      inference('sup-', [status(thm)], ['86', '87'])).
% 0.76/0.94  thf('89', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         ((r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1)
% 0.76/0.94          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.76/0.94          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.76/0.94          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.76/0.94          | (r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1))),
% 0.76/0.94      inference('sup-', [status(thm)], ['85', '88'])).
% 0.76/0.94  thf('90', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         (~ (r1_xboole_0 @ X0 @ X0)
% 0.76/0.94          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.76/0.94          | (r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1))),
% 0.76/0.94      inference('simplify', [status(thm)], ['89'])).
% 0.76/0.94  thf('91', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.76/0.94          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['82', '90'])).
% 0.76/0.94  thf('92', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.76/0.94          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['82', '90'])).
% 0.76/0.94  thf('93', plain,
% 0.76/0.94      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.76/0.94         (~ (r2_hidden @ X2 @ X0)
% 0.76/0.94          | ~ (r2_hidden @ X2 @ X3)
% 0.76/0.94          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.76/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/0.94  thf('94', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         (((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1))
% 0.76/0.94          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.76/0.94          | ~ (r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X2))),
% 0.76/0.94      inference('sup-', [status(thm)], ['92', '93'])).
% 0.76/0.94  thf('95', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1))
% 0.76/0.94          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.76/0.94          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['91', '94'])).
% 0.76/0.94  thf('96', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (~ (r1_xboole_0 @ X0 @ X0) | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.76/0.94      inference('simplify', [status(thm)], ['95'])).
% 0.76/0.94  thf('97', plain,
% 0.76/0.94      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.76/0.94         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['81', '96'])).
% 0.76/0.94  thf('98', plain,
% 0.76/0.94      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.94      inference('split', [status(esa)], ['2'])).
% 0.76/0.94  thf('99', plain,
% 0.76/0.94      ((![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.76/0.94         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.94      inference('demod', [status(thm)], ['97', '98'])).
% 0.76/0.94  thf('100', plain,
% 0.76/0.94      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.76/0.94         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('split', [status(esa)], ['45'])).
% 0.76/0.94  thf('101', plain,
% 0.76/0.94      ((((sk_A) != (k1_xboole_0)))
% 0.76/0.94         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.76/0.94             (((sk_A) = (k1_xboole_0))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['99', '100'])).
% 0.76/0.94  thf('102', plain,
% 0.76/0.94      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.94      inference('split', [status(esa)], ['2'])).
% 0.76/0.94  thf('103', plain,
% 0.76/0.94      ((((sk_A) != (sk_A)))
% 0.76/0.94         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.76/0.94             (((sk_A) = (k1_xboole_0))))),
% 0.76/0.94      inference('demod', [status(thm)], ['101', '102'])).
% 0.76/0.94  thf('104', plain,
% 0.76/0.94      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.76/0.94       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.76/0.94      inference('simplify', [status(thm)], ['103'])).
% 0.76/0.94  thf('105', plain,
% 0.76/0.94      ((((sk_A) = (k1_xboole_0))) | 
% 0.76/0.94       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.76/0.94       (((sk_B_1) = (k1_xboole_0)))),
% 0.76/0.94      inference('split', [status(esa)], ['2'])).
% 0.76/0.94  thf('106', plain, ($false),
% 0.76/0.94      inference('sat_resolution*', [status(thm)],
% 0.76/0.94                ['1', '50', '51', '72', '104', '105'])).
% 0.76/0.94  
% 0.76/0.94  % SZS output end Refutation
% 0.76/0.94  
% 0.76/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

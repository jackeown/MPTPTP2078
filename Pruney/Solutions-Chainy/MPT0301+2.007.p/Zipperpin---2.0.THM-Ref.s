%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FYh4Ch2zQb

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:00 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 171 expanded)
%              Number of leaves         :   24 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  796 (1415 expanded)
%              Number of equality atoms :  107 ( 221 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ( ( sk_B_2 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( r1_xboole_0 @ X7 @ X7 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('5',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( r1_xboole_0 @ sk_B_2 @ k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('8',plain,
    ( ( r1_xboole_0 @ sk_B_2 @ sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('10',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ~ ( r1_tarski @ sk_B_2 @ sk_B_2 ) )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','12'])).

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

thf('14',plain,(
    ! [X20: $i,X21: $i,X24: $i] :
      ( ( X24
        = ( k2_zfmisc_1 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X24 @ X20 @ X21 ) @ ( sk_E @ X24 @ X20 @ X21 ) @ ( sk_D @ X24 @ X20 @ X21 ) @ X20 @ X21 )
      | ( r2_hidden @ ( sk_D @ X24 @ X20 @ X21 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ X14 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ sk_B_2 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('27',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v1_xboole_0 @ sk_B_2 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','30'])).

thf('32',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('33',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('34',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('35',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X16 )
      | ~ ( r2_hidden @ X11 @ X16 )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ( X13
       != ( k4_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    ! [X11: $i,X12: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X11 @ X16 )
      | ( zip_tseitin_0 @ X12 @ X11 @ ( k4_tarski @ X11 @ X12 ) @ X14 @ X16 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_B_1 @ X0 ) @ X2 @ ( k4_tarski @ X2 @ ( sk_B_1 @ X0 ) ) @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_B_1 @ X1 ) @ ( sk_B_1 @ X0 ) @ ( k4_tarski @ ( sk_B_1 @ X0 ) @ ( sk_B_1 @ X1 ) ) @ X1 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X19 @ X22 )
      | ( X22
       != ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X21 @ X20 ) )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X0 ) @ ( sk_B_1 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('47',plain,
    ( ( ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ( ( sk_B_2 != sk_B_2 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('52',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('55',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf('56',plain,
    ( ( r1_xboole_0 @ sk_A @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('58',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('60',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ~ ( r1_tarski @ sk_A @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X20: $i,X21: $i,X24: $i] :
      ( ( X24
        = ( k2_zfmisc_1 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X24 @ X20 @ X21 ) @ ( sk_E @ X24 @ X20 @ X21 ) @ ( sk_D @ X24 @ X20 @ X21 ) @ X20 @ X21 )
      | ( r2_hidden @ ( sk_D @ X24 @ X20 @ X21 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('64',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X11 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ sk_A )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('74',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','74'])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('77',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','31','32','53','75','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FYh4Ch2zQb
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.67  % Solved by: fo/fo7.sh
% 0.47/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.67  % done 401 iterations in 0.223s
% 0.47/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.67  % SZS output start Refutation
% 0.47/0.67  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.47/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.67  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.47/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.47/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.67  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.47/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.67  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.47/0.67  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.47/0.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.47/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.67  thf(t113_zfmisc_1, conjecture,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.67       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.67    (~( ![A:$i,B:$i]:
% 0.47/0.67        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.67          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.47/0.67    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.67  thf('0', plain,
% 0.47/0.67      ((((sk_B_2) != (k1_xboole_0))
% 0.47/0.67        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) != (k1_xboole_0)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('1', plain,
% 0.47/0.67      (~ (((sk_B_2) = (k1_xboole_0))) | 
% 0.47/0.67       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.47/0.67      inference('split', [status(esa)], ['0'])).
% 0.47/0.67  thf('2', plain,
% 0.47/0.67      ((((sk_B_2) = (k1_xboole_0))
% 0.47/0.67        | ((sk_A) = (k1_xboole_0))
% 0.47/0.67        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('3', plain,
% 0.47/0.67      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('split', [status(esa)], ['2'])).
% 0.47/0.67  thf(t66_xboole_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.47/0.67       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.47/0.67  thf('4', plain,
% 0.47/0.67      (![X7 : $i]: ((r1_xboole_0 @ X7 @ X7) | ((X7) != (k1_xboole_0)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.47/0.67  thf('5', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.67      inference('simplify', [status(thm)], ['4'])).
% 0.47/0.67  thf('6', plain,
% 0.47/0.67      (((r1_xboole_0 @ sk_B_2 @ k1_xboole_0)) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup+', [status(thm)], ['3', '5'])).
% 0.47/0.67  thf('7', plain,
% 0.47/0.67      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('split', [status(esa)], ['2'])).
% 0.47/0.67  thf('8', plain,
% 0.47/0.67      (((r1_xboole_0 @ sk_B_2 @ sk_B_2)) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['6', '7'])).
% 0.47/0.67  thf(t69_xboole_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.67       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.47/0.67  thf('9', plain,
% 0.47/0.67      (![X9 : $i, X10 : $i]:
% 0.47/0.67         (~ (r1_xboole_0 @ X9 @ X10)
% 0.47/0.67          | ~ (r1_tarski @ X9 @ X10)
% 0.47/0.67          | (v1_xboole_0 @ X9))),
% 0.47/0.67      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.47/0.67  thf('10', plain,
% 0.47/0.67      ((((v1_xboole_0 @ sk_B_2) | ~ (r1_tarski @ sk_B_2 @ sk_B_2)))
% 0.47/0.67         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.67  thf(d10_xboole_0, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.67  thf('11', plain,
% 0.47/0.67      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.47/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.67  thf('12', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.47/0.67      inference('simplify', [status(thm)], ['11'])).
% 0.47/0.67  thf('13', plain,
% 0.47/0.67      (((v1_xboole_0 @ sk_B_2)) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['10', '12'])).
% 0.47/0.67  thf(d2_zfmisc_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.47/0.67       ( ![D:$i]:
% 0.47/0.67         ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.67           ( ?[E:$i,F:$i]:
% 0.47/0.67             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.47/0.67               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.47/0.67  thf(zf_stmt_2, axiom,
% 0.47/0.67    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.47/0.67     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.47/0.67       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.47/0.67         ( r2_hidden @ E @ A ) ) ))).
% 0.47/0.67  thf(zf_stmt_3, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.47/0.67       ( ![D:$i]:
% 0.47/0.67         ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.67           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.47/0.67  thf('14', plain,
% 0.47/0.67      (![X20 : $i, X21 : $i, X24 : $i]:
% 0.47/0.67         (((X24) = (k2_zfmisc_1 @ X21 @ X20))
% 0.47/0.67          | (zip_tseitin_0 @ (sk_F @ X24 @ X20 @ X21) @ 
% 0.47/0.67             (sk_E @ X24 @ X20 @ X21) @ (sk_D @ X24 @ X20 @ X21) @ X20 @ X21)
% 0.47/0.67          | (r2_hidden @ (sk_D @ X24 @ X20 @ X21) @ X24))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.67  thf('15', plain,
% 0.47/0.67      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.47/0.67         ((r2_hidden @ X12 @ X14)
% 0.47/0.67          | ~ (zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.67  thf('16', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.47/0.67          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.47/0.67          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.47/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.67  thf(d1_xboole_0, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.47/0.67  thf('17', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.67  thf('18', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 0.47/0.67          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.47/0.67          | ~ (v1_xboole_0 @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['16', '17'])).
% 0.47/0.67  thf('19', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.67  thf('20', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         (~ (v1_xboole_0 @ X2)
% 0.47/0.67          | ((X2) = (k2_zfmisc_1 @ X1 @ X0))
% 0.47/0.67          | ~ (v1_xboole_0 @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.67  thf('21', plain,
% 0.47/0.67      ((((sk_A) != (k1_xboole_0))
% 0.47/0.67        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) != (k1_xboole_0)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('22', plain,
% 0.47/0.67      ((((k2_zfmisc_1 @ sk_A @ sk_B_2) != (k1_xboole_0)))
% 0.47/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('split', [status(esa)], ['21'])).
% 0.47/0.67  thf('23', plain,
% 0.47/0.67      ((![X0 : $i]:
% 0.47/0.67          (((X0) != (k1_xboole_0))
% 0.47/0.67           | ~ (v1_xboole_0 @ sk_B_2)
% 0.47/0.67           | ~ (v1_xboole_0 @ X0)))
% 0.47/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['20', '22'])).
% 0.47/0.67  thf('24', plain,
% 0.47/0.67      (((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_2)))
% 0.47/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('simplify', [status(thm)], ['23'])).
% 0.47/0.67  thf('25', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.67      inference('simplify', [status(thm)], ['4'])).
% 0.47/0.67  thf('26', plain,
% 0.47/0.67      (![X9 : $i, X10 : $i]:
% 0.47/0.67         (~ (r1_xboole_0 @ X9 @ X10)
% 0.47/0.67          | ~ (r1_tarski @ X9 @ X10)
% 0.47/0.67          | (v1_xboole_0 @ X9))),
% 0.47/0.67      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.47/0.67  thf('27', plain,
% 0.47/0.67      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.67  thf('28', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.47/0.67      inference('simplify', [status(thm)], ['11'])).
% 0.47/0.67  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.67      inference('demod', [status(thm)], ['27', '28'])).
% 0.47/0.67  thf('30', plain,
% 0.47/0.67      ((~ (v1_xboole_0 @ sk_B_2))
% 0.47/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('simplify_reflect+', [status(thm)], ['24', '29'])).
% 0.47/0.67  thf('31', plain,
% 0.47/0.67      (~ (((sk_B_2) = (k1_xboole_0))) | 
% 0.47/0.67       (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['13', '30'])).
% 0.47/0.67  thf('32', plain,
% 0.47/0.67      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.47/0.67       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.47/0.67      inference('split', [status(esa)], ['21'])).
% 0.47/0.67  thf('33', plain,
% 0.47/0.67      ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))
% 0.47/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('split', [status(esa)], ['2'])).
% 0.47/0.67  thf(t7_xboole_0, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.67          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.47/0.67  thf('34', plain,
% 0.47/0.67      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.47/0.67      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.67  thf('35', plain,
% 0.47/0.67      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.47/0.67      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.67  thf('36', plain,
% 0.47/0.67      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.47/0.67         ((zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X16)
% 0.47/0.67          | ~ (r2_hidden @ X11 @ X16)
% 0.47/0.67          | ~ (r2_hidden @ X12 @ X14)
% 0.47/0.67          | ((X13) != (k4_tarski @ X11 @ X12)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.67  thf('37', plain,
% 0.47/0.67      (![X11 : $i, X12 : $i, X14 : $i, X16 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X12 @ X14)
% 0.47/0.67          | ~ (r2_hidden @ X11 @ X16)
% 0.47/0.67          | (zip_tseitin_0 @ X12 @ X11 @ (k4_tarski @ X11 @ X12) @ X14 @ X16))),
% 0.47/0.67      inference('simplify', [status(thm)], ['36'])).
% 0.47/0.67  thf('38', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         (((X0) = (k1_xboole_0))
% 0.47/0.67          | (zip_tseitin_0 @ (sk_B_1 @ X0) @ X2 @ 
% 0.47/0.67             (k4_tarski @ X2 @ (sk_B_1 @ X0)) @ X0 @ X1)
% 0.47/0.67          | ~ (r2_hidden @ X2 @ X1))),
% 0.47/0.67      inference('sup-', [status(thm)], ['35', '37'])).
% 0.47/0.67  thf('39', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (((X0) = (k1_xboole_0))
% 0.47/0.67          | (zip_tseitin_0 @ (sk_B_1 @ X1) @ (sk_B_1 @ X0) @ 
% 0.47/0.67             (k4_tarski @ (sk_B_1 @ X0) @ (sk_B_1 @ X1)) @ X1 @ X0)
% 0.47/0.67          | ((X1) = (k1_xboole_0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['34', '38'])).
% 0.47/0.67  thf('40', plain,
% 0.47/0.67      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.67         (~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.47/0.67          | (r2_hidden @ X19 @ X22)
% 0.47/0.67          | ((X22) != (k2_zfmisc_1 @ X21 @ X20)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.67  thf('41', plain,
% 0.47/0.67      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.67         ((r2_hidden @ X19 @ (k2_zfmisc_1 @ X21 @ X20))
% 0.47/0.67          | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 0.47/0.67      inference('simplify', [status(thm)], ['40'])).
% 0.47/0.67  thf('42', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (((X1) = (k1_xboole_0))
% 0.47/0.67          | ((X0) = (k1_xboole_0))
% 0.47/0.67          | (r2_hidden @ (k4_tarski @ (sk_B_1 @ X0) @ (sk_B_1 @ X1)) @ 
% 0.47/0.67             (k2_zfmisc_1 @ X0 @ X1)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['39', '41'])).
% 0.47/0.67  thf('43', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.67  thf('44', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (((X1) = (k1_xboole_0))
% 0.47/0.67          | ((X0) = (k1_xboole_0))
% 0.47/0.67          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.67  thf('45', plain,
% 0.47/0.67      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.67         | ((sk_B_2) = (k1_xboole_0))
% 0.47/0.67         | ((sk_A) = (k1_xboole_0))))
% 0.47/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['33', '44'])).
% 0.47/0.67  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.67      inference('demod', [status(thm)], ['27', '28'])).
% 0.47/0.67  thf('47', plain,
% 0.47/0.67      (((((sk_B_2) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.47/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.67  thf('48', plain,
% 0.47/0.67      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('split', [status(esa)], ['0'])).
% 0.47/0.67  thf('49', plain,
% 0.47/0.67      (((((sk_B_2) != (sk_B_2)) | ((sk_A) = (k1_xboole_0))))
% 0.47/0.67         <= (~ (((sk_B_2) = (k1_xboole_0))) & 
% 0.47/0.67             (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['47', '48'])).
% 0.47/0.67  thf('50', plain,
% 0.47/0.67      ((((sk_A) = (k1_xboole_0)))
% 0.47/0.67         <= (~ (((sk_B_2) = (k1_xboole_0))) & 
% 0.47/0.67             (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('simplify', [status(thm)], ['49'])).
% 0.47/0.67  thf('51', plain,
% 0.47/0.67      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('split', [status(esa)], ['21'])).
% 0.47/0.67  thf('52', plain,
% 0.47/0.67      ((((sk_A) != (sk_A)))
% 0.47/0.67         <= (~ (((sk_B_2) = (k1_xboole_0))) & 
% 0.47/0.67             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.47/0.67             (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.67  thf('53', plain,
% 0.47/0.67      ((((sk_A) = (k1_xboole_0))) | 
% 0.47/0.67       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))) | 
% 0.47/0.67       (((sk_B_2) = (k1_xboole_0)))),
% 0.47/0.67      inference('simplify', [status(thm)], ['52'])).
% 0.47/0.67  thf('54', plain,
% 0.47/0.67      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('split', [status(esa)], ['2'])).
% 0.47/0.67  thf('55', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.67      inference('simplify', [status(thm)], ['4'])).
% 0.47/0.67  thf('56', plain,
% 0.47/0.67      (((r1_xboole_0 @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup+', [status(thm)], ['54', '55'])).
% 0.47/0.67  thf('57', plain,
% 0.47/0.67      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('split', [status(esa)], ['2'])).
% 0.47/0.67  thf('58', plain,
% 0.47/0.67      (((r1_xboole_0 @ sk_A @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['56', '57'])).
% 0.47/0.67  thf('59', plain,
% 0.47/0.67      (![X9 : $i, X10 : $i]:
% 0.47/0.67         (~ (r1_xboole_0 @ X9 @ X10)
% 0.47/0.67          | ~ (r1_tarski @ X9 @ X10)
% 0.47/0.67          | (v1_xboole_0 @ X9))),
% 0.47/0.67      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.47/0.67  thf('60', plain,
% 0.47/0.67      ((((v1_xboole_0 @ sk_A) | ~ (r1_tarski @ sk_A @ sk_A)))
% 0.47/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['58', '59'])).
% 0.47/0.67  thf('61', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.47/0.67      inference('simplify', [status(thm)], ['11'])).
% 0.47/0.67  thf('62', plain, (((v1_xboole_0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['60', '61'])).
% 0.47/0.67  thf('63', plain,
% 0.47/0.67      (![X20 : $i, X21 : $i, X24 : $i]:
% 0.47/0.67         (((X24) = (k2_zfmisc_1 @ X21 @ X20))
% 0.47/0.67          | (zip_tseitin_0 @ (sk_F @ X24 @ X20 @ X21) @ 
% 0.47/0.67             (sk_E @ X24 @ X20 @ X21) @ (sk_D @ X24 @ X20 @ X21) @ X20 @ X21)
% 0.47/0.67          | (r2_hidden @ (sk_D @ X24 @ X20 @ X21) @ X24))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.67  thf('64', plain,
% 0.47/0.67      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.47/0.67         ((r2_hidden @ X11 @ X15)
% 0.47/0.67          | ~ (zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.67  thf('65', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.47/0.67          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.47/0.67          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['63', '64'])).
% 0.47/0.67  thf('66', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.67  thf('67', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         ((r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1)
% 0.47/0.67          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.47/0.67          | ~ (v1_xboole_0 @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['65', '66'])).
% 0.47/0.67  thf('68', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.67  thf('69', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         (~ (v1_xboole_0 @ X2)
% 0.47/0.67          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.47/0.67          | ~ (v1_xboole_0 @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['67', '68'])).
% 0.47/0.67  thf('70', plain,
% 0.47/0.67      ((((k2_zfmisc_1 @ sk_A @ sk_B_2) != (k1_xboole_0)))
% 0.47/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('split', [status(esa)], ['21'])).
% 0.47/0.67  thf('71', plain,
% 0.47/0.67      ((![X0 : $i]:
% 0.47/0.67          (((X0) != (k1_xboole_0))
% 0.47/0.67           | ~ (v1_xboole_0 @ sk_A)
% 0.47/0.67           | ~ (v1_xboole_0 @ X0)))
% 0.47/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['69', '70'])).
% 0.47/0.67  thf('72', plain,
% 0.47/0.67      (((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_A)))
% 0.47/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('simplify', [status(thm)], ['71'])).
% 0.47/0.67  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.67      inference('demod', [status(thm)], ['27', '28'])).
% 0.47/0.67  thf('74', plain,
% 0.47/0.67      ((~ (v1_xboole_0 @ sk_A))
% 0.47/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.47/0.67      inference('simplify_reflect+', [status(thm)], ['72', '73'])).
% 0.47/0.67  thf('75', plain,
% 0.47/0.67      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.47/0.67       (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['62', '74'])).
% 0.47/0.67  thf('76', plain,
% 0.47/0.67      ((((sk_A) = (k1_xboole_0))) | 
% 0.47/0.67       (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))) | 
% 0.47/0.67       (((sk_B_2) = (k1_xboole_0)))),
% 0.47/0.67      inference('split', [status(esa)], ['2'])).
% 0.47/0.67  thf('77', plain, ($false),
% 0.47/0.67      inference('sat_resolution*', [status(thm)],
% 0.47/0.67                ['1', '31', '32', '53', '75', '76'])).
% 0.47/0.67  
% 0.47/0.67  % SZS output end Refutation
% 0.47/0.67  
% 0.47/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

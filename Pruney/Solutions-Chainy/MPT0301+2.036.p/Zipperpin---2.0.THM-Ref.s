%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hcxw9jI30p

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:04 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 196 expanded)
%              Number of leaves         :   20 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          : 1035 (2096 expanded)
%              Number of equality atoms :  133 ( 278 expanded)
%              Maximal formula depth    :   16 (   8 average)

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

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

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

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
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

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

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

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X18 @ X15 @ X16 ) @ ( sk_E_1 @ X18 @ X15 @ X16 ) @ X18 @ X15 @ X16 )
      | ( X17
       != ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X18 @ X15 @ X16 ) @ ( sk_E_1 @ X18 @ X15 @ X16 ) @ X18 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ X9 )
      | ~ ( zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('12',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_F_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('18',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','23'])).

thf('25',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('31',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('34',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('35',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('36',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X11 )
      | ~ ( r2_hidden @ X6 @ X11 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ( X8
       != ( k4_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('38',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X6 @ X11 )
      | ( zip_tseitin_0 @ X7 @ X6 @ ( k4_tarski @ X6 @ X7 ) @ X9 @ X11 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_B @ X0 ) @ X2 @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_B @ X1 ) @ ( sk_B @ X0 ) @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ X1 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X14 @ X17 )
      | ( X17
       != ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('42',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X16 @ X15 ) )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('46',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_B @ X1 ) @ ( sk_B @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('50',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49','57'])).

thf('59',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('64',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('67',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('68',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('70',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X18 @ X15 @ X16 ) @ ( sk_E_1 @ X18 @ X15 @ X16 ) @ X18 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X6 @ X10 )
      | ~ ( zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('75',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','78'])).

thf('80',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('83',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('85',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('88',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','32','33','65','86','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hcxw9jI30p
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:17:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 292 iterations in 0.169s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.42/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.42/0.62  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.42/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.42/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.62  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.42/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.62  thf(t113_zfmisc_1, conjecture,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.42/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i,B:$i]:
% 0.42/0.62        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.42/0.62          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      ((((sk_B_1) != (k1_xboole_0))
% 0.42/0.62        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.42/0.62       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('split', [status(esa)], ['0'])).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      ((((sk_B_1) = (k1_xboole_0))
% 0.42/0.62        | ((sk_A) = (k1_xboole_0))
% 0.42/0.62        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['2'])).
% 0.42/0.62  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.42/0.62  thf('4', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.42/0.62      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.42/0.62  thf(t3_xboole_0, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.42/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.42/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.42/0.62            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.42/0.62  thf(d2_zfmisc_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.42/0.62       ( ![D:$i]:
% 0.42/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.42/0.62           ( ?[E:$i,F:$i]:
% 0.42/0.62             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.42/0.62               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.42/0.62  thf(zf_stmt_2, axiom,
% 0.42/0.62    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.42/0.62     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.42/0.62       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.42/0.62         ( r2_hidden @ E @ A ) ) ))).
% 0.42/0.62  thf(zf_stmt_3, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.42/0.62       ( ![D:$i]:
% 0.42/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.42/0.62           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X18 @ X17)
% 0.42/0.62          | (zip_tseitin_0 @ (sk_F_1 @ X18 @ X15 @ X16) @ 
% 0.42/0.62             (sk_E_1 @ X18 @ X15 @ X16) @ X18 @ X15 @ X16)
% 0.42/0.62          | ((X17) != (k2_zfmisc_1 @ X16 @ X15)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.42/0.62         ((zip_tseitin_0 @ (sk_F_1 @ X18 @ X15 @ X16) @ 
% 0.42/0.62           (sk_E_1 @ X18 @ X15 @ X16) @ X18 @ X15 @ X16)
% 0.42/0.62          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X16 @ X15)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['6'])).
% 0.42/0.62  thf('8', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ X2)
% 0.42/0.62          | (zip_tseitin_0 @ 
% 0.42/0.62             (sk_F_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.42/0.62             (sk_E_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.42/0.62             (sk_C @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['5', '7'])).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.42/0.62         ((r2_hidden @ X7 @ X9) | ~ (zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X10))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ X2)
% 0.42/0.62          | (r2_hidden @ 
% 0.42/0.62             (sk_F_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ X2)
% 0.42/0.62          | (r2_hidden @ 
% 0.42/0.62             (sk_F_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X2 @ X0)
% 0.42/0.62          | ~ (r2_hidden @ X2 @ X3)
% 0.42/0.62          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.42/0.62         ((r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ X2)
% 0.42/0.62          | ~ (r1_xboole_0 @ X0 @ X3)
% 0.42/0.62          | ~ (r2_hidden @ 
% 0.42/0.62               (sk_F_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ X3))),
% 0.42/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ X2)
% 0.42/0.62          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.42/0.62          | (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ X2))),
% 0.42/0.62      inference('sup-', [status(thm)], ['10', '13'])).
% 0.42/0.62  thf('15', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (~ (r1_xboole_0 @ X0 @ X0)
% 0.42/0.62          | (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ X2))),
% 0.42/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ k1_xboole_0) @ X0)),
% 0.42/0.62      inference('sup-', [status(thm)], ['4', '15'])).
% 0.42/0.62  thf(t7_xboole_0, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.42/0.62          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.42/0.62  thf('18', plain,
% 0.42/0.62      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.42/0.62  thf('19', plain,
% 0.42/0.62      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X2 @ X0)
% 0.42/0.62          | ~ (r2_hidden @ X2 @ X3)
% 0.42/0.62          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((X0) = (k1_xboole_0))
% 0.42/0.62          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.42/0.62          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.42/0.62  thf('21', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((X0) = (k1_xboole_0))
% 0.42/0.62          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.42/0.62          | ((X0) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['17', '20'])).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['21'])).
% 0.42/0.62  thf('23', plain,
% 0.42/0.62      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['16', '22'])).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      ((![X0 : $i]: ((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0)))
% 0.42/0.62         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup+', [status(thm)], ['3', '23'])).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['2'])).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      ((![X0 : $i]: ((k2_zfmisc_1 @ X0 @ sk_B_1) = (sk_B_1)))
% 0.42/0.62         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['24', '25'])).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      ((((sk_A) != (k1_xboole_0))
% 0.42/0.62        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.42/0.62         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['27'])).
% 0.42/0.62  thf('29', plain,
% 0.42/0.62      ((((sk_B_1) != (k1_xboole_0)))
% 0.42/0.62         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.42/0.62             (((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['26', '28'])).
% 0.42/0.62  thf('30', plain,
% 0.42/0.62      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['2'])).
% 0.42/0.62  thf('31', plain,
% 0.42/0.62      ((((sk_B_1) != (sk_B_1)))
% 0.42/0.62         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.42/0.62             (((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.42/0.62  thf('32', plain,
% 0.42/0.62      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.42/0.62       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['31'])).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.42/0.62       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('split', [status(esa)], ['27'])).
% 0.42/0.62  thf('34', plain,
% 0.42/0.62      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['2'])).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.42/0.62  thf('36', plain,
% 0.42/0.62      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.42/0.62  thf('37', plain,
% 0.42/0.62      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.42/0.62         ((zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X11)
% 0.42/0.62          | ~ (r2_hidden @ X6 @ X11)
% 0.42/0.62          | ~ (r2_hidden @ X7 @ X9)
% 0.42/0.62          | ((X8) != (k4_tarski @ X6 @ X7)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      (![X6 : $i, X7 : $i, X9 : $i, X11 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X7 @ X9)
% 0.42/0.62          | ~ (r2_hidden @ X6 @ X11)
% 0.42/0.62          | (zip_tseitin_0 @ X7 @ X6 @ (k4_tarski @ X6 @ X7) @ X9 @ X11))),
% 0.42/0.62      inference('simplify', [status(thm)], ['37'])).
% 0.42/0.62  thf('39', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (((X0) = (k1_xboole_0))
% 0.42/0.62          | (zip_tseitin_0 @ (sk_B @ X0) @ X2 @ 
% 0.42/0.62             (k4_tarski @ X2 @ (sk_B @ X0)) @ X0 @ X1)
% 0.42/0.62          | ~ (r2_hidden @ X2 @ X1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['36', '38'])).
% 0.42/0.62  thf('40', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((X0) = (k1_xboole_0))
% 0.42/0.62          | (zip_tseitin_0 @ (sk_B @ X1) @ (sk_B @ X0) @ 
% 0.42/0.62             (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ X1 @ X0)
% 0.42/0.62          | ((X1) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['35', '39'])).
% 0.42/0.62  thf('41', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.62         (~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.42/0.62          | (r2_hidden @ X14 @ X17)
% 0.42/0.62          | ((X17) != (k2_zfmisc_1 @ X16 @ X15)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.62  thf('42', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.42/0.62         ((r2_hidden @ X14 @ (k2_zfmisc_1 @ X16 @ X15))
% 0.42/0.62          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16))),
% 0.42/0.62      inference('simplify', [status(thm)], ['41'])).
% 0.42/0.62  thf('43', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((X1) = (k1_xboole_0))
% 0.42/0.62          | ((X0) = (k1_xboole_0))
% 0.42/0.62          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 0.42/0.62             (k2_zfmisc_1 @ X0 @ X1)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['40', '42'])).
% 0.42/0.62  thf('44', plain,
% 0.42/0.62      ((((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.42/0.62          k1_xboole_0)
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))
% 0.42/0.62         | ((sk_B_1) = (k1_xboole_0))))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup+', [status(thm)], ['34', '43'])).
% 0.42/0.62  thf('45', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((X1) = (k1_xboole_0))
% 0.42/0.62          | ((X0) = (k1_xboole_0))
% 0.42/0.62          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 0.42/0.62             (k2_zfmisc_1 @ X0 @ X1)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['40', '42'])).
% 0.42/0.62  thf('46', plain,
% 0.42/0.62      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X2 @ X0)
% 0.42/0.62          | ~ (r2_hidden @ X2 @ X3)
% 0.42/0.62          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.42/0.62  thf('47', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (((X1) = (k1_xboole_0))
% 0.42/0.62          | ((X0) = (k1_xboole_0))
% 0.42/0.62          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ X2)
% 0.42/0.62          | ~ (r2_hidden @ (k4_tarski @ (sk_B @ X1) @ (sk_B @ X0)) @ X2))),
% 0.42/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.42/0.62  thf('48', plain,
% 0.42/0.62      (((((sk_B_1) = (k1_xboole_0))
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))
% 0.42/0.62         | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ k1_xboole_0)
% 0.42/0.62         | ((sk_B_1) = (k1_xboole_0))
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['44', '47'])).
% 0.42/0.62  thf('49', plain,
% 0.42/0.62      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['2'])).
% 0.42/0.62  thf('50', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.42/0.62      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.42/0.62  thf('51', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.42/0.62  thf('52', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.42/0.62  thf('53', plain,
% 0.42/0.62      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X2 @ X0)
% 0.42/0.62          | ~ (r2_hidden @ X2 @ X3)
% 0.42/0.62          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.42/0.62  thf('54', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((r1_xboole_0 @ X0 @ X1)
% 0.42/0.62          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.42/0.62          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.42/0.62      inference('sup-', [status(thm)], ['52', '53'])).
% 0.42/0.62  thf('55', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((r1_xboole_0 @ X0 @ X1)
% 0.42/0.62          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.42/0.62          | (r1_xboole_0 @ X0 @ X1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['51', '54'])).
% 0.42/0.62  thf('56', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.42/0.62      inference('simplify', [status(thm)], ['55'])).
% 0.42/0.62  thf('57', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.42/0.62      inference('sup-', [status(thm)], ['50', '56'])).
% 0.42/0.62  thf('58', plain,
% 0.42/0.62      (((((sk_B_1) = (k1_xboole_0))
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))
% 0.42/0.62         | ((sk_B_1) = (k1_xboole_0))
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['48', '49', '57'])).
% 0.42/0.62  thf('59', plain,
% 0.42/0.62      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['58'])).
% 0.42/0.62  thf('60', plain,
% 0.42/0.62      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['0'])).
% 0.42/0.62  thf('61', plain,
% 0.42/0.62      (((((sk_B_1) != (sk_B_1)) | ((sk_A) = (k1_xboole_0))))
% 0.42/0.62         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.42/0.62             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['59', '60'])).
% 0.42/0.62  thf('62', plain,
% 0.42/0.62      ((((sk_A) = (k1_xboole_0)))
% 0.42/0.62         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.42/0.62             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['61'])).
% 0.42/0.62  thf('63', plain,
% 0.42/0.62      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['27'])).
% 0.42/0.62  thf('64', plain,
% 0.42/0.62      ((((sk_A) != (sk_A)))
% 0.42/0.62         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.42/0.62             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.42/0.62             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['62', '63'])).
% 0.42/0.62  thf('65', plain,
% 0.42/0.62      ((((sk_A) = (k1_xboole_0))) | 
% 0.42/0.62       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.42/0.62       (((sk_B_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['64'])).
% 0.42/0.62  thf('66', plain,
% 0.42/0.62      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['2'])).
% 0.42/0.62  thf('67', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.42/0.62      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.42/0.62  thf('68', plain,
% 0.42/0.62      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup+', [status(thm)], ['66', '67'])).
% 0.42/0.62  thf('69', plain,
% 0.42/0.62      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.42/0.62  thf('70', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.42/0.62         ((zip_tseitin_0 @ (sk_F_1 @ X18 @ X15 @ X16) @ 
% 0.42/0.62           (sk_E_1 @ X18 @ X15 @ X16) @ X18 @ X15 @ X16)
% 0.42/0.62          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X16 @ X15)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['6'])).
% 0.42/0.62  thf('71', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.42/0.62          | (zip_tseitin_0 @ 
% 0.42/0.62             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.42/0.62             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.42/0.62             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['69', '70'])).
% 0.42/0.62  thf('72', plain,
% 0.42/0.62      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.42/0.62         ((r2_hidden @ X6 @ X10) | ~ (zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X10))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.62  thf('73', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 0.42/0.62          | (r2_hidden @ 
% 0.42/0.62             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['71', '72'])).
% 0.42/0.62  thf('74', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 0.42/0.62          | (r2_hidden @ 
% 0.42/0.62             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['71', '72'])).
% 0.42/0.62  thf('75', plain,
% 0.42/0.62      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X2 @ X0)
% 0.42/0.62          | ~ (r2_hidden @ X2 @ X3)
% 0.42/0.62          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.42/0.62  thf('76', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 0.42/0.62          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.42/0.62          | ~ (r2_hidden @ 
% 0.42/0.62               (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X2))),
% 0.42/0.62      inference('sup-', [status(thm)], ['74', '75'])).
% 0.42/0.62  thf('77', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 0.42/0.62          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.42/0.62          | ((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['73', '76'])).
% 0.42/0.62  thf('78', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (r1_xboole_0 @ X0 @ X0) | ((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['77'])).
% 0.42/0.62  thf('79', plain,
% 0.42/0.62      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (k1_xboole_0)))
% 0.42/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['68', '78'])).
% 0.42/0.62  thf('80', plain,
% 0.42/0.62      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['2'])).
% 0.42/0.62  thf('81', plain,
% 0.42/0.62      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (sk_A)))
% 0.42/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['79', '80'])).
% 0.42/0.62  thf('82', plain,
% 0.42/0.62      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.42/0.62         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['27'])).
% 0.42/0.62  thf('83', plain,
% 0.42/0.62      ((((sk_A) != (k1_xboole_0)))
% 0.42/0.62         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.42/0.62             (((sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['81', '82'])).
% 0.42/0.62  thf('84', plain,
% 0.42/0.62      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['2'])).
% 0.42/0.62  thf('85', plain,
% 0.42/0.62      ((((sk_A) != (sk_A)))
% 0.42/0.62         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.42/0.62             (((sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['83', '84'])).
% 0.42/0.62  thf('86', plain,
% 0.42/0.62      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.42/0.62       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['85'])).
% 0.42/0.62  thf('87', plain,
% 0.42/0.62      ((((sk_A) = (k1_xboole_0))) | 
% 0.42/0.62       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.42/0.62       (((sk_B_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('split', [status(esa)], ['2'])).
% 0.42/0.62  thf('88', plain, ($false),
% 0.42/0.62      inference('sat_resolution*', [status(thm)],
% 0.42/0.62                ['1', '32', '33', '65', '86', '87'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.45/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

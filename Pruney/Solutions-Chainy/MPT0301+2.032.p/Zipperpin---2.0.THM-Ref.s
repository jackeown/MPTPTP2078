%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2nEHeC72Ml

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:03 EST 2020

% Result     : Theorem 6.99s
% Output     : Refutation 6.99s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 306 expanded)
%              Number of leaves         :   19 (  88 expanded)
%              Depth                    :   16
%              Number of atoms          :  960 (2822 expanded)
%              Number of equality atoms :  128 ( 368 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

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

thf('2',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ( X18
        = ( k2_zfmisc_1 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X18 @ X14 @ X15 ) @ ( sk_E @ X18 @ X14 @ X15 ) @ ( sk_D @ X18 @ X14 @ X15 ) @ X14 @ X15 )
      | ( r2_hidden @ ( sk_D @ X18 @ X14 @ X15 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ X8 )
      | ~ ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k5_xboole_0 @ X0 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ ( k5_xboole_0 @ X0 @ X0 ) )
       != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ ( k5_xboole_0 @ X0 @ X0 ) )
       != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_xboole_0 != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('26',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('29',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('30',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ( X18
        = ( k2_zfmisc_1 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X18 @ X14 @ X15 ) @ ( sk_E @ X18 @ X14 @ X15 ) @ ( sk_D @ X18 @ X14 @ X15 ) @ X14 @ X15 )
      | ( r2_hidden @ ( sk_D @ X18 @ X14 @ X15 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X5 @ X9 )
      | ~ ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('39',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('42',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('46',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('48',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ ( k2_zfmisc_1 @ X22 @ X25 ) )
      | ~ ( r2_hidden @ X23 @ X25 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) @ ( sk_D @ X2 @ k1_xboole_0 @ X3 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('52',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ( X18
        = ( k2_zfmisc_1 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X18 @ X14 @ X15 ) @ ( sk_E @ X18 @ X14 @ X15 ) @ ( sk_D @ X18 @ X14 @ X15 ) @ X14 @ X15 )
      | ( r2_hidden @ ( sk_D @ X18 @ X14 @ X15 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15 )
      | ( r2_hidden @ X13 @ X16 )
      | ( X16
       != ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X15 @ X14 ) )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k5_xboole_0 @ X0 @ X0 ) @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( ( k5_xboole_0 @ X0 @ X0 )
        = ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k5_xboole_0 @ X2 @ X2 )
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','60'])).

thf('62',plain,
    ( ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_B @ sk_A ) @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','61'])).

thf('63',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('65',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','64'])).

thf('66',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['63','65'])).

thf('67',plain,
    ( ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_B @ sk_A ) @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['62','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('69',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('71',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('78',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k5_xboole_0 @ X0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ sk_B )
       != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ sk_B )
       != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k1_xboole_0 != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('86',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','27','28','72','73','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2nEHeC72Ml
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:04:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 6.99/7.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.99/7.18  % Solved by: fo/fo7.sh
% 6.99/7.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.99/7.18  % done 4392 iterations in 6.715s
% 6.99/7.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.99/7.18  % SZS output start Refutation
% 6.99/7.18  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 6.99/7.18  thf(sk_B_type, type, sk_B: $i).
% 6.99/7.18  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 6.99/7.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.99/7.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.99/7.18  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 6.99/7.18  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 6.99/7.18  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 6.99/7.18  thf(sk_A_type, type, sk_A: $i).
% 6.99/7.18  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.99/7.18  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 6.99/7.18  thf(t113_zfmisc_1, conjecture,
% 6.99/7.18    (![A:$i,B:$i]:
% 6.99/7.18     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.99/7.18       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.99/7.18  thf(zf_stmt_0, negated_conjecture,
% 6.99/7.18    (~( ![A:$i,B:$i]:
% 6.99/7.18        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.99/7.18          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 6.99/7.18    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 6.99/7.18  thf('0', plain,
% 6.99/7.18      ((((sk_B) != (k1_xboole_0))
% 6.99/7.18        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 6.99/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.99/7.18  thf('1', plain,
% 6.99/7.18      (~ (((sk_B) = (k1_xboole_0))) | 
% 6.99/7.18       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 6.99/7.18      inference('split', [status(esa)], ['0'])).
% 6.99/7.18  thf(d2_zfmisc_1, axiom,
% 6.99/7.18    (![A:$i,B:$i,C:$i]:
% 6.99/7.18     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 6.99/7.18       ( ![D:$i]:
% 6.99/7.18         ( ( r2_hidden @ D @ C ) <=>
% 6.99/7.18           ( ?[E:$i,F:$i]:
% 6.99/7.18             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 6.99/7.18               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 6.99/7.18  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 6.99/7.18  thf(zf_stmt_2, axiom,
% 6.99/7.18    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 6.99/7.18     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 6.99/7.18       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 6.99/7.18         ( r2_hidden @ E @ A ) ) ))).
% 6.99/7.18  thf(zf_stmt_3, axiom,
% 6.99/7.18    (![A:$i,B:$i,C:$i]:
% 6.99/7.18     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 6.99/7.18       ( ![D:$i]:
% 6.99/7.18         ( ( r2_hidden @ D @ C ) <=>
% 6.99/7.18           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 6.99/7.18  thf('2', plain,
% 6.99/7.18      (![X14 : $i, X15 : $i, X18 : $i]:
% 6.99/7.18         (((X18) = (k2_zfmisc_1 @ X15 @ X14))
% 6.99/7.18          | (zip_tseitin_0 @ (sk_F @ X18 @ X14 @ X15) @ 
% 6.99/7.18             (sk_E @ X18 @ X14 @ X15) @ (sk_D @ X18 @ X14 @ X15) @ X14 @ X15)
% 6.99/7.18          | (r2_hidden @ (sk_D @ X18 @ X14 @ X15) @ X18))),
% 6.99/7.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.99/7.18  thf('3', plain,
% 6.99/7.18      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 6.99/7.18         ((r2_hidden @ X6 @ X8) | ~ (zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9))),
% 6.99/7.18      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.99/7.18  thf('4', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.99/7.18         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 6.99/7.18          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 6.99/7.18          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 6.99/7.18      inference('sup-', [status(thm)], ['2', '3'])).
% 6.99/7.18  thf(t92_xboole_1, axiom,
% 6.99/7.18    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 6.99/7.18  thf('5', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 6.99/7.18      inference('cnf', [status(esa)], [t92_xboole_1])).
% 6.99/7.18  thf(t1_xboole_0, axiom,
% 6.99/7.18    (![A:$i,B:$i,C:$i]:
% 6.99/7.18     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 6.99/7.18       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 6.99/7.18  thf('6', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.99/7.18         (~ (r2_hidden @ X0 @ X1)
% 6.99/7.18          | ~ (r2_hidden @ X0 @ X2)
% 6.99/7.18          | ~ (r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 6.99/7.18      inference('cnf', [status(esa)], [t1_xboole_0])).
% 6.99/7.18  thf('7', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i]:
% 6.99/7.18         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 6.99/7.18          | ~ (r2_hidden @ X1 @ X0)
% 6.99/7.18          | ~ (r2_hidden @ X1 @ X0))),
% 6.99/7.18      inference('sup-', [status(thm)], ['5', '6'])).
% 6.99/7.18  thf('8', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i]:
% 6.99/7.18         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 6.99/7.18      inference('simplify', [status(thm)], ['7'])).
% 6.99/7.18  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.99/7.18      inference('condensation', [status(thm)], ['8'])).
% 6.99/7.18  thf('10', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i]:
% 6.99/7.18         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 6.99/7.18          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 6.99/7.18      inference('sup-', [status(thm)], ['4', '9'])).
% 6.99/7.18  thf('11', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 6.99/7.18      inference('cnf', [status(esa)], [t92_xboole_1])).
% 6.99/7.18  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.99/7.18      inference('condensation', [status(thm)], ['8'])).
% 6.99/7.18  thf('13', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 6.99/7.18      inference('sup-', [status(thm)], ['11', '12'])).
% 6.99/7.18  thf('14', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i]:
% 6.99/7.18         ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 6.99/7.18      inference('sup-', [status(thm)], ['10', '13'])).
% 6.99/7.18  thf('15', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 6.99/7.18      inference('cnf', [status(esa)], [t92_xboole_1])).
% 6.99/7.18  thf('16', plain,
% 6.99/7.18      ((((sk_B) = (k1_xboole_0))
% 6.99/7.18        | ((sk_A) = (k1_xboole_0))
% 6.99/7.18        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 6.99/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.99/7.18  thf('17', plain,
% 6.99/7.18      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 6.99/7.18      inference('split', [status(esa)], ['16'])).
% 6.99/7.18  thf('18', plain,
% 6.99/7.18      ((![X0 : $i]: ((sk_B) = (k5_xboole_0 @ X0 @ X0)))
% 6.99/7.18         <= ((((sk_B) = (k1_xboole_0))))),
% 6.99/7.18      inference('sup+', [status(thm)], ['15', '17'])).
% 6.99/7.18  thf('19', plain,
% 6.99/7.18      ((((sk_A) != (k1_xboole_0))
% 6.99/7.18        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 6.99/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.99/7.18  thf('20', plain,
% 6.99/7.18      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 6.99/7.18         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 6.99/7.18      inference('split', [status(esa)], ['19'])).
% 6.99/7.18  thf('21', plain,
% 6.99/7.18      ((![X0 : $i]:
% 6.99/7.18          ((k2_zfmisc_1 @ sk_A @ (k5_xboole_0 @ X0 @ X0)) != (k1_xboole_0)))
% 6.99/7.18         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 6.99/7.18             (((sk_B) = (k1_xboole_0))))),
% 6.99/7.18      inference('sup-', [status(thm)], ['18', '20'])).
% 6.99/7.18  thf('22', plain,
% 6.99/7.18      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 6.99/7.18      inference('split', [status(esa)], ['16'])).
% 6.99/7.18  thf('23', plain,
% 6.99/7.18      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ (k5_xboole_0 @ X0 @ X0)) != (sk_B)))
% 6.99/7.18         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 6.99/7.18             (((sk_B) = (k1_xboole_0))))),
% 6.99/7.18      inference('demod', [status(thm)], ['21', '22'])).
% 6.99/7.18  thf('24', plain,
% 6.99/7.18      ((((k1_xboole_0) != (sk_B)))
% 6.99/7.18         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 6.99/7.18             (((sk_B) = (k1_xboole_0))))),
% 6.99/7.18      inference('sup-', [status(thm)], ['14', '23'])).
% 6.99/7.18  thf('25', plain,
% 6.99/7.18      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 6.99/7.18      inference('split', [status(esa)], ['16'])).
% 6.99/7.18  thf('26', plain,
% 6.99/7.18      ((((sk_B) != (sk_B)))
% 6.99/7.18         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 6.99/7.18             (((sk_B) = (k1_xboole_0))))),
% 6.99/7.18      inference('demod', [status(thm)], ['24', '25'])).
% 6.99/7.18  thf('27', plain,
% 6.99/7.18      (~ (((sk_B) = (k1_xboole_0))) | 
% 6.99/7.18       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 6.99/7.18      inference('simplify', [status(thm)], ['26'])).
% 6.99/7.18  thf('28', plain,
% 6.99/7.18      (~ (((sk_A) = (k1_xboole_0))) | 
% 6.99/7.18       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 6.99/7.18      inference('split', [status(esa)], ['19'])).
% 6.99/7.18  thf('29', plain,
% 6.99/7.18      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 6.99/7.18         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 6.99/7.18      inference('split', [status(esa)], ['16'])).
% 6.99/7.18  thf('30', plain,
% 6.99/7.18      (![X14 : $i, X15 : $i, X18 : $i]:
% 6.99/7.18         (((X18) = (k2_zfmisc_1 @ X15 @ X14))
% 6.99/7.18          | (zip_tseitin_0 @ (sk_F @ X18 @ X14 @ X15) @ 
% 6.99/7.18             (sk_E @ X18 @ X14 @ X15) @ (sk_D @ X18 @ X14 @ X15) @ X14 @ X15)
% 6.99/7.18          | (r2_hidden @ (sk_D @ X18 @ X14 @ X15) @ X18))),
% 6.99/7.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.99/7.18  thf('31', plain,
% 6.99/7.18      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 6.99/7.18         ((r2_hidden @ X5 @ X9) | ~ (zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9))),
% 6.99/7.18      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.99/7.18  thf('32', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.99/7.18         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 6.99/7.18          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 6.99/7.18          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 6.99/7.18      inference('sup-', [status(thm)], ['30', '31'])).
% 6.99/7.18  thf('33', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.99/7.18      inference('condensation', [status(thm)], ['8'])).
% 6.99/7.18  thf('34', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i]:
% 6.99/7.18         (((X1) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 6.99/7.18          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1))),
% 6.99/7.18      inference('sup-', [status(thm)], ['32', '33'])).
% 6.99/7.18  thf('35', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.99/7.18         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 6.99/7.18          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 6.99/7.18          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 6.99/7.18      inference('sup-', [status(thm)], ['30', '31'])).
% 6.99/7.18  thf('36', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.99/7.18      inference('condensation', [status(thm)], ['8'])).
% 6.99/7.18  thf('37', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i]:
% 6.99/7.18         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 6.99/7.18          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 6.99/7.18      inference('sup-', [status(thm)], ['35', '36'])).
% 6.99/7.18  thf('38', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.99/7.18      inference('condensation', [status(thm)], ['8'])).
% 6.99/7.18  thf('39', plain,
% 6.99/7.18      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 6.99/7.18      inference('sup-', [status(thm)], ['37', '38'])).
% 6.99/7.18  thf('40', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i]:
% 6.99/7.18         (((X1) = (k1_xboole_0))
% 6.99/7.18          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1))),
% 6.99/7.18      inference('demod', [status(thm)], ['34', '39'])).
% 6.99/7.18  thf('41', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.99/7.18         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 6.99/7.18          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 6.99/7.18          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 6.99/7.18      inference('sup-', [status(thm)], ['2', '3'])).
% 6.99/7.18  thf('42', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.99/7.18      inference('condensation', [status(thm)], ['8'])).
% 6.99/7.18  thf('43', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i]:
% 6.99/7.18         (((X1) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 6.99/7.18          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 6.99/7.18      inference('sup-', [status(thm)], ['41', '42'])).
% 6.99/7.18  thf('44', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i]:
% 6.99/7.18         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 6.99/7.18          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 6.99/7.18      inference('sup-', [status(thm)], ['4', '9'])).
% 6.99/7.18  thf('45', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.99/7.18      inference('condensation', [status(thm)], ['8'])).
% 6.99/7.18  thf('46', plain,
% 6.99/7.18      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 6.99/7.18      inference('sup-', [status(thm)], ['44', '45'])).
% 6.99/7.18  thf('47', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i]:
% 6.99/7.18         (((X1) = (k1_xboole_0))
% 6.99/7.18          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 6.99/7.18      inference('demod', [status(thm)], ['43', '46'])).
% 6.99/7.18  thf(l54_zfmisc_1, axiom,
% 6.99/7.18    (![A:$i,B:$i,C:$i,D:$i]:
% 6.99/7.18     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 6.99/7.18       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 6.99/7.18  thf('48', plain,
% 6.99/7.18      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 6.99/7.18         ((r2_hidden @ (k4_tarski @ X21 @ X23) @ (k2_zfmisc_1 @ X22 @ X25))
% 6.99/7.18          | ~ (r2_hidden @ X23 @ X25)
% 6.99/7.18          | ~ (r2_hidden @ X21 @ X22))),
% 6.99/7.18      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 6.99/7.18  thf('49', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.99/7.18         (((X0) = (k1_xboole_0))
% 6.99/7.18          | ~ (r2_hidden @ X3 @ X2)
% 6.99/7.18          | (r2_hidden @ (k4_tarski @ X3 @ (sk_D @ X0 @ k1_xboole_0 @ X1)) @ 
% 6.99/7.18             (k2_zfmisc_1 @ X2 @ X0)))),
% 6.99/7.18      inference('sup-', [status(thm)], ['47', '48'])).
% 6.99/7.18  thf('50', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.99/7.18         (((X0) = (k1_xboole_0))
% 6.99/7.18          | (r2_hidden @ 
% 6.99/7.18             (k4_tarski @ (sk_D @ X0 @ X1 @ k1_xboole_0) @ 
% 6.99/7.18              (sk_D @ X2 @ k1_xboole_0 @ X3)) @ 
% 6.99/7.18             (k2_zfmisc_1 @ X0 @ X2))
% 6.99/7.18          | ((X2) = (k1_xboole_0)))),
% 6.99/7.18      inference('sup-', [status(thm)], ['40', '49'])).
% 6.99/7.18  thf('51', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 6.99/7.18      inference('cnf', [status(esa)], [t92_xboole_1])).
% 6.99/7.18  thf('52', plain,
% 6.99/7.18      (![X14 : $i, X15 : $i, X18 : $i]:
% 6.99/7.18         (((X18) = (k2_zfmisc_1 @ X15 @ X14))
% 6.99/7.18          | (zip_tseitin_0 @ (sk_F @ X18 @ X14 @ X15) @ 
% 6.99/7.18             (sk_E @ X18 @ X14 @ X15) @ (sk_D @ X18 @ X14 @ X15) @ X14 @ X15)
% 6.99/7.18          | (r2_hidden @ (sk_D @ X18 @ X14 @ X15) @ X18))),
% 6.99/7.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.99/7.18  thf('53', plain,
% 6.99/7.18      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 6.99/7.18         (~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15)
% 6.99/7.18          | (r2_hidden @ X13 @ X16)
% 6.99/7.18          | ((X16) != (k2_zfmisc_1 @ X15 @ X14)))),
% 6.99/7.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.99/7.18  thf('54', plain,
% 6.99/7.18      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 6.99/7.18         ((r2_hidden @ X13 @ (k2_zfmisc_1 @ X15 @ X14))
% 6.99/7.18          | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15))),
% 6.99/7.18      inference('simplify', [status(thm)], ['53'])).
% 6.99/7.18  thf('55', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.99/7.18         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 6.99/7.18          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 6.99/7.18          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 6.99/7.18      inference('sup-', [status(thm)], ['52', '54'])).
% 6.99/7.18  thf('56', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 6.99/7.18      inference('sup-', [status(thm)], ['11', '12'])).
% 6.99/7.18  thf('57', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.99/7.18         ((r2_hidden @ (sk_D @ (k5_xboole_0 @ X0 @ X0) @ X2 @ X1) @ 
% 6.99/7.18           (k2_zfmisc_1 @ X1 @ X2))
% 6.99/7.18          | ((k5_xboole_0 @ X0 @ X0) = (k2_zfmisc_1 @ X1 @ X2)))),
% 6.99/7.18      inference('sup-', [status(thm)], ['55', '56'])).
% 6.99/7.18  thf('58', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.99/7.18         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ (k2_zfmisc_1 @ X1 @ X0))
% 6.99/7.18          | ((k5_xboole_0 @ X2 @ X2) = (k2_zfmisc_1 @ X1 @ X0)))),
% 6.99/7.18      inference('sup+', [status(thm)], ['51', '57'])).
% 6.99/7.18  thf('59', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 6.99/7.18      inference('sup-', [status(thm)], ['11', '12'])).
% 6.99/7.18  thf('60', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i, X3 : $i]:
% 6.99/7.18         (~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X1 @ X0))
% 6.99/7.18          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ 
% 6.99/7.18             (k2_zfmisc_1 @ X1 @ X0)))),
% 6.99/7.18      inference('sup-', [status(thm)], ['58', '59'])).
% 6.99/7.18  thf('61', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i]:
% 6.99/7.18         (((X0) = (k1_xboole_0))
% 6.99/7.18          | ((X1) = (k1_xboole_0))
% 6.99/7.18          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ 
% 6.99/7.18             (k2_zfmisc_1 @ X1 @ X0)))),
% 6.99/7.18      inference('sup-', [status(thm)], ['50', '60'])).
% 6.99/7.18  thf('62', plain,
% 6.99/7.18      ((((r2_hidden @ (sk_D @ k1_xboole_0 @ sk_B @ sk_A) @ k1_xboole_0)
% 6.99/7.18         | ((sk_A) = (k1_xboole_0))
% 6.99/7.18         | ((sk_B) = (k1_xboole_0))))
% 6.99/7.18         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 6.99/7.18      inference('sup+', [status(thm)], ['29', '61'])).
% 6.99/7.18  thf('63', plain,
% 6.99/7.18      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 6.99/7.18      inference('split', [status(esa)], ['0'])).
% 6.99/7.18  thf('64', plain,
% 6.99/7.18      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 6.99/7.18       ~ (((sk_B) = (k1_xboole_0)))),
% 6.99/7.18      inference('simplify', [status(thm)], ['26'])).
% 6.99/7.18  thf('65', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 6.99/7.18      inference('sat_resolution*', [status(thm)], ['1', '64'])).
% 6.99/7.18  thf('66', plain, (((sk_B) != (k1_xboole_0))),
% 6.99/7.18      inference('simpl_trail', [status(thm)], ['63', '65'])).
% 6.99/7.18  thf('67', plain,
% 6.99/7.18      ((((r2_hidden @ (sk_D @ k1_xboole_0 @ sk_B @ sk_A) @ k1_xboole_0)
% 6.99/7.18         | ((sk_A) = (k1_xboole_0))))
% 6.99/7.18         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 6.99/7.18      inference('simplify_reflect-', [status(thm)], ['62', '66'])).
% 6.99/7.18  thf('68', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.99/7.18      inference('condensation', [status(thm)], ['8'])).
% 6.99/7.18  thf('69', plain,
% 6.99/7.18      ((((sk_A) = (k1_xboole_0)))
% 6.99/7.18         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 6.99/7.18      inference('clc', [status(thm)], ['67', '68'])).
% 6.99/7.18  thf('70', plain,
% 6.99/7.18      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 6.99/7.18      inference('split', [status(esa)], ['19'])).
% 6.99/7.18  thf('71', plain,
% 6.99/7.18      ((((sk_A) != (sk_A)))
% 6.99/7.18         <= (~ (((sk_A) = (k1_xboole_0))) & 
% 6.99/7.18             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 6.99/7.18      inference('sup-', [status(thm)], ['69', '70'])).
% 6.99/7.18  thf('72', plain,
% 6.99/7.18      ((((sk_A) = (k1_xboole_0))) | 
% 6.99/7.18       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 6.99/7.18      inference('simplify', [status(thm)], ['71'])).
% 6.99/7.18  thf('73', plain,
% 6.99/7.18      ((((sk_A) = (k1_xboole_0))) | 
% 6.99/7.18       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 6.99/7.18       (((sk_B) = (k1_xboole_0)))),
% 6.99/7.18      inference('split', [status(esa)], ['16'])).
% 6.99/7.18  thf('74', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i]:
% 6.99/7.18         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 6.99/7.18          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 6.99/7.18      inference('sup-', [status(thm)], ['35', '36'])).
% 6.99/7.18  thf('75', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 6.99/7.18      inference('sup-', [status(thm)], ['11', '12'])).
% 6.99/7.18  thf('76', plain,
% 6.99/7.18      (![X0 : $i, X1 : $i]:
% 6.99/7.18         ((k1_xboole_0) = (k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 6.99/7.18      inference('sup-', [status(thm)], ['74', '75'])).
% 6.99/7.18  thf('77', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 6.99/7.18      inference('cnf', [status(esa)], [t92_xboole_1])).
% 6.99/7.18  thf('78', plain,
% 6.99/7.18      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 6.99/7.18      inference('split', [status(esa)], ['16'])).
% 6.99/7.18  thf('79', plain,
% 6.99/7.18      ((![X0 : $i]: ((sk_A) = (k5_xboole_0 @ X0 @ X0)))
% 6.99/7.18         <= ((((sk_A) = (k1_xboole_0))))),
% 6.99/7.18      inference('sup+', [status(thm)], ['77', '78'])).
% 6.99/7.18  thf('80', plain,
% 6.99/7.18      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 6.99/7.18         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 6.99/7.18      inference('split', [status(esa)], ['19'])).
% 6.99/7.18  thf('81', plain,
% 6.99/7.18      ((![X0 : $i]:
% 6.99/7.18          ((k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ sk_B) != (k1_xboole_0)))
% 6.99/7.18         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 6.99/7.18             (((sk_A) = (k1_xboole_0))))),
% 6.99/7.18      inference('sup-', [status(thm)], ['79', '80'])).
% 6.99/7.18  thf('82', plain,
% 6.99/7.18      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 6.99/7.18      inference('split', [status(esa)], ['16'])).
% 6.99/7.18  thf('83', plain,
% 6.99/7.18      ((![X0 : $i]: ((k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ sk_B) != (sk_A)))
% 6.99/7.18         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 6.99/7.18             (((sk_A) = (k1_xboole_0))))),
% 6.99/7.18      inference('demod', [status(thm)], ['81', '82'])).
% 6.99/7.18  thf('84', plain,
% 6.99/7.18      ((((k1_xboole_0) != (sk_A)))
% 6.99/7.18         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 6.99/7.18             (((sk_A) = (k1_xboole_0))))),
% 6.99/7.18      inference('sup-', [status(thm)], ['76', '83'])).
% 6.99/7.18  thf('85', plain,
% 6.99/7.18      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 6.99/7.18      inference('split', [status(esa)], ['16'])).
% 6.99/7.18  thf('86', plain,
% 6.99/7.18      ((((sk_A) != (sk_A)))
% 6.99/7.18         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 6.99/7.18             (((sk_A) = (k1_xboole_0))))),
% 6.99/7.18      inference('demod', [status(thm)], ['84', '85'])).
% 6.99/7.18  thf('87', plain,
% 6.99/7.18      (~ (((sk_A) = (k1_xboole_0))) | 
% 6.99/7.18       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 6.99/7.18      inference('simplify', [status(thm)], ['86'])).
% 6.99/7.18  thf('88', plain, ($false),
% 6.99/7.18      inference('sat_resolution*', [status(thm)],
% 6.99/7.18                ['1', '27', '28', '72', '73', '87'])).
% 6.99/7.18  
% 6.99/7.18  % SZS output end Refutation
% 6.99/7.18  
% 6.99/7.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.k7UIMw67KR

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:03 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 256 expanded)
%              Number of leaves         :   19 (  73 expanded)
%              Depth                    :   17
%              Number of atoms          :  708 (2391 expanded)
%              Number of equality atoms :  105 ( 325 expanded)
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

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

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
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
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

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('14',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('22',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('25',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('31',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ ( k2_zfmisc_1 @ X22 @ X25 ) )
      | ~ ( r2_hidden @ X23 @ X25 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ ( sk_D @ X2 @ k1_xboole_0 @ X3 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) @ ( sk_D @ sk_B @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
        | ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','36'])).

thf('38',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('40',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','39'])).

thf('41',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['38','40'])).

thf('42',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) @ ( sk_D @ sk_B @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['37','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('44',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('46',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('49',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ( X18
        = ( k2_zfmisc_1 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X18 @ X14 @ X15 ) @ ( sk_E @ X18 @ X14 @ X15 ) @ ( sk_D @ X18 @ X14 @ X15 ) @ X14 @ X15 )
      | ( r2_hidden @ ( sk_D @ X18 @ X14 @ X15 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X5 @ X9 )
      | ~ ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('55',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('56',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('61',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('63',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','47','48','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.k7UIMw67KR
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:43:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 171 iterations in 0.173s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.45/0.65  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.45/0.65  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.65  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.65  thf(t113_zfmisc_1, conjecture,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i]:
% 0.45/0.65        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.65          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      ((((sk_B) != (k1_xboole_0))
% 0.45/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.45/0.65       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.45/0.65      inference('split', [status(esa)], ['0'])).
% 0.45/0.65  thf(d2_zfmisc_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.45/0.65       ( ![D:$i]:
% 0.45/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.65           ( ?[E:$i,F:$i]:
% 0.45/0.65             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.45/0.65               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.45/0.65  thf(zf_stmt_2, axiom,
% 0.45/0.65    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.45/0.65     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.45/0.65       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.45/0.65         ( r2_hidden @ E @ A ) ) ))).
% 0.45/0.65  thf(zf_stmt_3, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.45/0.65       ( ![D:$i]:
% 0.45/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.65           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X14 : $i, X15 : $i, X18 : $i]:
% 0.45/0.65         (((X18) = (k2_zfmisc_1 @ X15 @ X14))
% 0.45/0.65          | (zip_tseitin_0 @ (sk_F @ X18 @ X14 @ X15) @ 
% 0.45/0.65             (sk_E @ X18 @ X14 @ X15) @ (sk_D @ X18 @ X14 @ X15) @ X14 @ X15)
% 0.45/0.65          | (r2_hidden @ (sk_D @ X18 @ X14 @ X15) @ X18))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.65         ((r2_hidden @ X6 @ X8) | ~ (zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.45/0.65          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.45/0.65          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.65  thf(t5_boole, axiom,
% 0.45/0.65    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.65  thf('5', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.65  thf(t1_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.45/0.65       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.65          | ~ (r2_hidden @ X0 @ X2)
% 0.45/0.65          | ~ (r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X1 @ X0)
% 0.45/0.65          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.45/0.65          | ~ (r2_hidden @ X1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['7'])).
% 0.45/0.65  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.45/0.65      inference('condensation', [status(thm)], ['8'])).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.45/0.65          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['4', '9'])).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      ((((sk_B) = (k1_xboole_0))
% 0.45/0.65        | ((sk_A) = (k1_xboole_0))
% 0.45/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['11'])).
% 0.45/0.65  thf('13', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.45/0.65      inference('condensation', [status(thm)], ['8'])).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.45/0.65         <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['10', '14'])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['11'])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      ((![X0 : $i]: ((sk_B) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.45/0.65         <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.65      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      ((((sk_A) != (k1_xboole_0))
% 0.45/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.45/0.65         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['18'])).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      ((((sk_B) != (k1_xboole_0)))
% 0.45/0.65         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.45/0.65             (((sk_B) = (k1_xboole_0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['17', '19'])).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['11'])).
% 0.45/0.65  thf('22', plain,
% 0.45/0.65      ((((sk_B) != (sk_B)))
% 0.45/0.65         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.45/0.65             (((sk_B) = (k1_xboole_0))))),
% 0.45/0.65      inference('demod', [status(thm)], ['20', '21'])).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.45/0.65       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['22'])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.45/0.65       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.45/0.65      inference('split', [status(esa)], ['18'])).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.45/0.65         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['11'])).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.45/0.65          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.45/0.65          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.65  thf('27', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.45/0.65      inference('condensation', [status(thm)], ['8'])).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((X1) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 0.45/0.65          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.45/0.65          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['4', '9'])).
% 0.45/0.65  thf('30', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.45/0.65      inference('condensation', [status(thm)], ['8'])).
% 0.45/0.65  thf('31', plain,
% 0.45/0.65      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((X1) = (k1_xboole_0))
% 0.45/0.65          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.45/0.65      inference('demod', [status(thm)], ['28', '31'])).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((X1) = (k1_xboole_0))
% 0.45/0.65          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.45/0.65      inference('demod', [status(thm)], ['28', '31'])).
% 0.45/0.65  thf(l54_zfmisc_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.45/0.65       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.45/0.65  thf('34', plain,
% 0.45/0.65      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.45/0.65         ((r2_hidden @ (k4_tarski @ X21 @ X23) @ (k2_zfmisc_1 @ X22 @ X25))
% 0.45/0.65          | ~ (r2_hidden @ X23 @ X25)
% 0.45/0.65          | ~ (r2_hidden @ X21 @ X22))),
% 0.45/0.65      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.45/0.65  thf('35', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.65         (((X0) = (k1_xboole_0))
% 0.45/0.65          | ~ (r2_hidden @ X3 @ X2)
% 0.45/0.65          | (r2_hidden @ (k4_tarski @ X3 @ (sk_D @ X0 @ k1_xboole_0 @ X1)) @ 
% 0.45/0.65             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.65  thf('36', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.65         (((X0) = (k1_xboole_0))
% 0.45/0.65          | (r2_hidden @ 
% 0.45/0.65             (k4_tarski @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ 
% 0.45/0.65              (sk_D @ X2 @ k1_xboole_0 @ X3)) @ 
% 0.45/0.65             (k2_zfmisc_1 @ X0 @ X2))
% 0.45/0.65          | ((X2) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['32', '35'])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      ((![X0 : $i, X1 : $i]:
% 0.45/0.65          ((r2_hidden @ 
% 0.45/0.65            (k4_tarski @ (sk_D @ sk_A @ k1_xboole_0 @ X1) @ 
% 0.45/0.65             (sk_D @ sk_B @ k1_xboole_0 @ X0)) @ 
% 0.45/0.65            k1_xboole_0)
% 0.45/0.65           | ((sk_B) = (k1_xboole_0))
% 0.45/0.65           | ((sk_A) = (k1_xboole_0))))
% 0.45/0.65         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.45/0.65      inference('sup+', [status(thm)], ['25', '36'])).
% 0.45/0.65  thf('38', plain,
% 0.45/0.65      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['0'])).
% 0.45/0.65  thf('39', plain,
% 0.45/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.45/0.65       ~ (((sk_B) = (k1_xboole_0)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['22'])).
% 0.45/0.65  thf('40', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.45/0.65      inference('sat_resolution*', [status(thm)], ['1', '39'])).
% 0.45/0.65  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['38', '40'])).
% 0.45/0.65  thf('42', plain,
% 0.45/0.65      ((![X0 : $i, X1 : $i]:
% 0.45/0.65          ((r2_hidden @ 
% 0.45/0.65            (k4_tarski @ (sk_D @ sk_A @ k1_xboole_0 @ X1) @ 
% 0.45/0.65             (sk_D @ sk_B @ k1_xboole_0 @ X0)) @ 
% 0.45/0.65            k1_xboole_0)
% 0.45/0.65           | ((sk_A) = (k1_xboole_0))))
% 0.45/0.65         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.45/0.65      inference('simplify_reflect-', [status(thm)], ['37', '41'])).
% 0.45/0.65  thf('43', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.45/0.65      inference('condensation', [status(thm)], ['8'])).
% 0.45/0.65  thf('44', plain,
% 0.45/0.65      ((((sk_A) = (k1_xboole_0)))
% 0.45/0.65         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.45/0.65      inference('clc', [status(thm)], ['42', '43'])).
% 0.45/0.65  thf('45', plain,
% 0.45/0.65      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['18'])).
% 0.45/0.65  thf('46', plain,
% 0.45/0.65      ((((sk_A) != (sk_A)))
% 0.45/0.65         <= (~ (((sk_A) = (k1_xboole_0))) & 
% 0.45/0.65             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.45/0.65  thf('47', plain,
% 0.45/0.65      ((((sk_A) = (k1_xboole_0))) | 
% 0.45/0.65       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['46'])).
% 0.45/0.65  thf('48', plain,
% 0.45/0.65      ((((sk_A) = (k1_xboole_0))) | 
% 0.45/0.65       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.45/0.65       (((sk_B) = (k1_xboole_0)))),
% 0.45/0.65      inference('split', [status(esa)], ['11'])).
% 0.45/0.65  thf('49', plain,
% 0.45/0.65      (![X14 : $i, X15 : $i, X18 : $i]:
% 0.45/0.65         (((X18) = (k2_zfmisc_1 @ X15 @ X14))
% 0.45/0.65          | (zip_tseitin_0 @ (sk_F @ X18 @ X14 @ X15) @ 
% 0.45/0.65             (sk_E @ X18 @ X14 @ X15) @ (sk_D @ X18 @ X14 @ X15) @ X14 @ X15)
% 0.45/0.65          | (r2_hidden @ (sk_D @ X18 @ X14 @ X15) @ X18))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.65  thf('50', plain,
% 0.45/0.65      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.65         ((r2_hidden @ X5 @ X9) | ~ (zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.65  thf('51', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.45/0.65          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.45/0.65          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.65  thf('52', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.45/0.65      inference('condensation', [status(thm)], ['8'])).
% 0.45/0.65  thf('53', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.45/0.65          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['51', '52'])).
% 0.45/0.65  thf('54', plain,
% 0.45/0.65      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['11'])).
% 0.45/0.65  thf('55', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.45/0.65      inference('condensation', [status(thm)], ['8'])).
% 0.45/0.65  thf('56', plain,
% 0.45/0.65      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['54', '55'])).
% 0.45/0.65  thf('57', plain,
% 0.45/0.65      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.45/0.65         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['53', '56'])).
% 0.45/0.65  thf('58', plain,
% 0.45/0.65      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['11'])).
% 0.45/0.65  thf('59', plain,
% 0.45/0.65      ((![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.45/0.65         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.65      inference('demod', [status(thm)], ['57', '58'])).
% 0.45/0.65  thf('60', plain,
% 0.45/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.45/0.65         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['18'])).
% 0.45/0.65  thf('61', plain,
% 0.45/0.65      ((((sk_A) != (k1_xboole_0)))
% 0.45/0.65         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.45/0.65             (((sk_A) = (k1_xboole_0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['59', '60'])).
% 0.45/0.65  thf('62', plain,
% 0.45/0.65      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['11'])).
% 0.45/0.65  thf('63', plain,
% 0.45/0.65      ((((sk_A) != (sk_A)))
% 0.45/0.65         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.45/0.65             (((sk_A) = (k1_xboole_0))))),
% 0.45/0.65      inference('demod', [status(thm)], ['61', '62'])).
% 0.45/0.65  thf('64', plain,
% 0.45/0.65      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.45/0.65       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['63'])).
% 0.45/0.65  thf('65', plain, ($false),
% 0.45/0.65      inference('sat_resolution*', [status(thm)],
% 0.45/0.65                ['1', '23', '24', '47', '48', '64'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

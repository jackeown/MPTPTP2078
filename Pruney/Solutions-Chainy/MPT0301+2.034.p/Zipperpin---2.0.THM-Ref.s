%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hpDB2JTiiR

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:03 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 147 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  680 (1241 expanded)
%              Number of equality atoms :  107 ( 218 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X39: $i,X40: $i,X43: $i] :
      ( ( X43
        = ( k2_zfmisc_1 @ X40 @ X39 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X43 @ X39 @ X40 ) @ ( sk_E @ X43 @ X39 @ X40 ) @ ( sk_D @ X43 @ X39 @ X40 ) @ X39 @ X40 )
      | ( r2_hidden @ ( sk_D @ X43 @ X39 @ X40 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ X31 @ X33 )
      | ~ ( zip_tseitin_0 @ X31 @ X30 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('6',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X51 @ X52 ) @ X53 )
      | ~ ( r2_hidden @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('7',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('12',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X51 @ X52 ) @ X53 )
      | ~ ( r2_hidden @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('14',plain,
    ( ! [X1: $i] :
        ~ ( r2_hidden @ X1 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

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
    inference(split,[status(esa)],['9'])).

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
    inference(split,[status(esa)],['9'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('27',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('30',plain,(
    ! [X46: $i,X47: $i,X48: $i,X50: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X46 @ X48 ) @ ( k2_zfmisc_1 @ X47 @ X50 ) )
      | ~ ( r2_hidden @ X48 @ X50 )
      | ~ ( r2_hidden @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( sk_C @ X1 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( k1_xboole_0 = X1 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ( k1_xboole_0 = sk_B )
      | ( k1_xboole_0 = sk_A ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('35',plain,
    ( ( ( k1_xboole_0 = sk_A )
      | ( k1_xboole_0 = sk_B ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( ( sk_B != sk_B )
      | ( k1_xboole_0 = sk_A ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_xboole_0 = sk_A )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('40',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X39: $i,X40: $i,X43: $i] :
      ( ( X43
        = ( k2_zfmisc_1 @ X40 @ X39 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X43 @ X39 @ X40 ) @ ( sk_E @ X43 @ X39 @ X40 ) @ ( sk_D @ X43 @ X39 @ X40 ) @ X39 @ X40 )
      | ( r2_hidden @ ( sk_D @ X43 @ X39 @ X40 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ X30 @ X34 )
      | ~ ( zip_tseitin_0 @ X31 @ X30 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('48',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('49',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X51 @ X52 ) @ X53 )
      | ~ ( r2_hidden @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('51',plain,
    ( ! [X1: $i] :
        ~ ( r2_hidden @ X1 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('56',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('58',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('61',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','41','59','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hpDB2JTiiR
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.74  % Solved by: fo/fo7.sh
% 0.53/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.74  % done 285 iterations in 0.279s
% 0.53/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.74  % SZS output start Refutation
% 0.53/0.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.53/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.74  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.53/0.74  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.53/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.53/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.74  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.53/0.74  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.53/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.53/0.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.53/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.74  thf(t113_zfmisc_1, conjecture,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.53/0.74       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.53/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.74    (~( ![A:$i,B:$i]:
% 0.53/0.74        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.53/0.74          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.53/0.74    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.53/0.74  thf('0', plain,
% 0.53/0.74      ((((sk_B) != (k1_xboole_0))
% 0.53/0.74        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('1', plain,
% 0.53/0.74      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.53/0.74       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.53/0.74      inference('split', [status(esa)], ['0'])).
% 0.53/0.74  thf(d2_zfmisc_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.53/0.74       ( ![D:$i]:
% 0.53/0.74         ( ( r2_hidden @ D @ C ) <=>
% 0.53/0.74           ( ?[E:$i,F:$i]:
% 0.53/0.74             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.53/0.74               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.53/0.74  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.53/0.74  thf(zf_stmt_2, axiom,
% 0.53/0.74    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.53/0.74     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.53/0.74       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.53/0.74         ( r2_hidden @ E @ A ) ) ))).
% 0.53/0.74  thf(zf_stmt_3, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.53/0.74       ( ![D:$i]:
% 0.53/0.74         ( ( r2_hidden @ D @ C ) <=>
% 0.53/0.74           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.53/0.74  thf('2', plain,
% 0.53/0.74      (![X39 : $i, X40 : $i, X43 : $i]:
% 0.53/0.74         (((X43) = (k2_zfmisc_1 @ X40 @ X39))
% 0.53/0.74          | (zip_tseitin_0 @ (sk_F @ X43 @ X39 @ X40) @ 
% 0.53/0.74             (sk_E @ X43 @ X39 @ X40) @ (sk_D @ X43 @ X39 @ X40) @ X39 @ X40)
% 0.53/0.74          | (r2_hidden @ (sk_D @ X43 @ X39 @ X40) @ X43))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.53/0.74  thf('3', plain,
% 0.53/0.74      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.53/0.74         ((r2_hidden @ X31 @ X33)
% 0.53/0.74          | ~ (zip_tseitin_0 @ X31 @ X30 @ X32 @ X33 @ X34))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.53/0.74  thf('4', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.53/0.74          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.53/0.74          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.53/0.74      inference('sup-', [status(thm)], ['2', '3'])).
% 0.53/0.74  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.53/0.74  thf('5', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.53/0.74      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.53/0.74  thf(t55_zfmisc_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.53/0.74  thf('6', plain,
% 0.53/0.74      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.53/0.74         (~ (r1_xboole_0 @ (k2_tarski @ X51 @ X52) @ X53)
% 0.53/0.74          | ~ (r2_hidden @ X51 @ X53))),
% 0.53/0.74      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.53/0.74  thf('7', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.53/0.74      inference('sup-', [status(thm)], ['5', '6'])).
% 0.53/0.74  thf('8', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.53/0.74          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['4', '7'])).
% 0.53/0.74  thf('9', plain,
% 0.53/0.74      ((((sk_B) = (k1_xboole_0))
% 0.53/0.74        | ((sk_A) = (k1_xboole_0))
% 0.53/0.74        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('10', plain,
% 0.53/0.74      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('split', [status(esa)], ['9'])).
% 0.53/0.74  thf('11', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.53/0.74      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.53/0.74  thf('12', plain,
% 0.53/0.74      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.53/0.74  thf('13', plain,
% 0.53/0.74      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.53/0.74         (~ (r1_xboole_0 @ (k2_tarski @ X51 @ X52) @ X53)
% 0.53/0.74          | ~ (r2_hidden @ X51 @ X53))),
% 0.53/0.74      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.53/0.74  thf('14', plain,
% 0.53/0.74      ((![X1 : $i]: ~ (r2_hidden @ X1 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['12', '13'])).
% 0.53/0.74  thf('15', plain,
% 0.53/0.74      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.53/0.74         <= ((((sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['8', '14'])).
% 0.53/0.74  thf('16', plain,
% 0.53/0.74      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('split', [status(esa)], ['9'])).
% 0.53/0.74  thf('17', plain,
% 0.53/0.74      ((![X0 : $i]: ((sk_B) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.53/0.74         <= ((((sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('demod', [status(thm)], ['15', '16'])).
% 0.53/0.74  thf('18', plain,
% 0.53/0.74      ((((sk_A) != (k1_xboole_0))
% 0.53/0.74        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('19', plain,
% 0.53/0.74      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.53/0.74         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('split', [status(esa)], ['18'])).
% 0.53/0.74  thf('20', plain,
% 0.53/0.74      ((((sk_B) != (k1_xboole_0)))
% 0.53/0.74         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.53/0.74             (((sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['17', '19'])).
% 0.53/0.74  thf('21', plain,
% 0.53/0.74      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('split', [status(esa)], ['9'])).
% 0.53/0.74  thf('22', plain,
% 0.53/0.74      ((((sk_B) != (sk_B)))
% 0.53/0.74         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.53/0.74             (((sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('demod', [status(thm)], ['20', '21'])).
% 0.53/0.74  thf('23', plain,
% 0.53/0.74      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.53/0.74       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.53/0.74      inference('simplify', [status(thm)], ['22'])).
% 0.53/0.74  thf('24', plain,
% 0.53/0.74      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.53/0.74       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.53/0.74      inference('split', [status(esa)], ['18'])).
% 0.53/0.74  thf('25', plain,
% 0.53/0.74      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.53/0.74         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('split', [status(esa)], ['9'])).
% 0.53/0.74  thf(t2_tarski, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.53/0.74       ( ( A ) = ( B ) ) ))).
% 0.53/0.74  thf('26', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((X1) = (X0))
% 0.53/0.74          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.53/0.74          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.53/0.74      inference('cnf', [status(esa)], [t2_tarski])).
% 0.53/0.74  thf('27', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.53/0.74      inference('sup-', [status(thm)], ['5', '6'])).
% 0.53/0.74  thf('28', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((k1_xboole_0) = (X0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['26', '27'])).
% 0.53/0.74  thf('29', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((k1_xboole_0) = (X0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['26', '27'])).
% 0.53/0.74  thf(l54_zfmisc_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.74     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.53/0.74       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.53/0.74  thf('30', plain,
% 0.53/0.74      (![X46 : $i, X47 : $i, X48 : $i, X50 : $i]:
% 0.53/0.74         ((r2_hidden @ (k4_tarski @ X46 @ X48) @ (k2_zfmisc_1 @ X47 @ X50))
% 0.53/0.74          | ~ (r2_hidden @ X48 @ X50)
% 0.53/0.74          | ~ (r2_hidden @ X46 @ X47))),
% 0.53/0.74      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.53/0.74  thf('31', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         (((k1_xboole_0) = (X0))
% 0.53/0.74          | ~ (r2_hidden @ X2 @ X1)
% 0.53/0.74          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C @ X0 @ k1_xboole_0)) @ 
% 0.53/0.74             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['29', '30'])).
% 0.53/0.74  thf('32', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k1_xboole_0) = (X0))
% 0.53/0.74          | (r2_hidden @ 
% 0.53/0.74             (k4_tarski @ (sk_C @ X0 @ k1_xboole_0) @ (sk_C @ X1 @ k1_xboole_0)) @ 
% 0.53/0.74             (k2_zfmisc_1 @ X0 @ X1))
% 0.53/0.74          | ((k1_xboole_0) = (X1)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['28', '31'])).
% 0.53/0.74  thf('33', plain,
% 0.53/0.74      ((((r2_hidden @ 
% 0.53/0.74          (k4_tarski @ (sk_C @ sk_A @ k1_xboole_0) @ 
% 0.53/0.74           (sk_C @ sk_B @ k1_xboole_0)) @ 
% 0.53/0.74          k1_xboole_0)
% 0.53/0.74         | ((k1_xboole_0) = (sk_B))
% 0.53/0.74         | ((k1_xboole_0) = (sk_A))))
% 0.53/0.74         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup+', [status(thm)], ['25', '32'])).
% 0.53/0.74  thf('34', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.53/0.74      inference('sup-', [status(thm)], ['5', '6'])).
% 0.53/0.74  thf('35', plain,
% 0.53/0.74      (((((k1_xboole_0) = (sk_A)) | ((k1_xboole_0) = (sk_B))))
% 0.53/0.74         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('clc', [status(thm)], ['33', '34'])).
% 0.53/0.74  thf('36', plain,
% 0.53/0.74      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('split', [status(esa)], ['0'])).
% 0.53/0.74  thf('37', plain,
% 0.53/0.74      (((((sk_B) != (sk_B)) | ((k1_xboole_0) = (sk_A))))
% 0.53/0.74         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.53/0.74             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['35', '36'])).
% 0.53/0.74  thf('38', plain,
% 0.53/0.74      ((((k1_xboole_0) = (sk_A)))
% 0.53/0.74         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.53/0.74             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('simplify', [status(thm)], ['37'])).
% 0.53/0.74  thf('39', plain,
% 0.53/0.74      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.53/0.74      inference('split', [status(esa)], ['18'])).
% 0.53/0.74  thf('40', plain,
% 0.53/0.74      ((((sk_A) != (sk_A)))
% 0.53/0.74         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.53/0.74             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.53/0.74             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['38', '39'])).
% 0.53/0.74  thf('41', plain,
% 0.53/0.74      ((((sk_A) = (k1_xboole_0))) | 
% 0.53/0.74       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.53/0.74       (((sk_B) = (k1_xboole_0)))),
% 0.53/0.74      inference('simplify', [status(thm)], ['40'])).
% 0.53/0.74  thf('42', plain,
% 0.53/0.74      (![X39 : $i, X40 : $i, X43 : $i]:
% 0.53/0.74         (((X43) = (k2_zfmisc_1 @ X40 @ X39))
% 0.53/0.74          | (zip_tseitin_0 @ (sk_F @ X43 @ X39 @ X40) @ 
% 0.53/0.74             (sk_E @ X43 @ X39 @ X40) @ (sk_D @ X43 @ X39 @ X40) @ X39 @ X40)
% 0.53/0.74          | (r2_hidden @ (sk_D @ X43 @ X39 @ X40) @ X43))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.53/0.74  thf('43', plain,
% 0.53/0.74      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.53/0.74         ((r2_hidden @ X30 @ X34)
% 0.53/0.74          | ~ (zip_tseitin_0 @ X31 @ X30 @ X32 @ X33 @ X34))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.53/0.74  thf('44', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.53/0.74          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.53/0.74          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['42', '43'])).
% 0.53/0.74  thf('45', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.53/0.74      inference('sup-', [status(thm)], ['5', '6'])).
% 0.53/0.74  thf('46', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.53/0.74          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['44', '45'])).
% 0.53/0.74  thf('47', plain,
% 0.53/0.74      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.53/0.74      inference('split', [status(esa)], ['9'])).
% 0.53/0.74  thf('48', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.53/0.74      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.53/0.74  thf('49', plain,
% 0.53/0.74      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup+', [status(thm)], ['47', '48'])).
% 0.53/0.74  thf('50', plain,
% 0.53/0.74      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.53/0.74         (~ (r1_xboole_0 @ (k2_tarski @ X51 @ X52) @ X53)
% 0.53/0.74          | ~ (r2_hidden @ X51 @ X53))),
% 0.53/0.74      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.53/0.74  thf('51', plain,
% 0.53/0.74      ((![X1 : $i]: ~ (r2_hidden @ X1 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['49', '50'])).
% 0.53/0.74  thf('52', plain,
% 0.53/0.74      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.53/0.74         <= ((((sk_A) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['46', '51'])).
% 0.53/0.74  thf('53', plain,
% 0.53/0.74      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.53/0.74      inference('split', [status(esa)], ['9'])).
% 0.53/0.74  thf('54', plain,
% 0.53/0.74      ((![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.53/0.74         <= ((((sk_A) = (k1_xboole_0))))),
% 0.53/0.74      inference('demod', [status(thm)], ['52', '53'])).
% 0.53/0.74  thf('55', plain,
% 0.53/0.74      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.53/0.74         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.53/0.74      inference('split', [status(esa)], ['18'])).
% 0.53/0.74  thf('56', plain,
% 0.53/0.74      ((((sk_A) != (k1_xboole_0)))
% 0.53/0.74         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.53/0.74             (((sk_A) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['54', '55'])).
% 0.53/0.74  thf('57', plain,
% 0.53/0.74      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.53/0.74      inference('split', [status(esa)], ['9'])).
% 0.53/0.74  thf('58', plain,
% 0.53/0.74      ((((sk_A) != (sk_A)))
% 0.53/0.74         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.53/0.74             (((sk_A) = (k1_xboole_0))))),
% 0.53/0.74      inference('demod', [status(thm)], ['56', '57'])).
% 0.53/0.74  thf('59', plain,
% 0.53/0.74      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.53/0.74       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.53/0.74      inference('simplify', [status(thm)], ['58'])).
% 0.53/0.74  thf('60', plain,
% 0.53/0.74      ((((sk_A) = (k1_xboole_0))) | 
% 0.53/0.74       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.53/0.74       (((sk_B) = (k1_xboole_0)))),
% 0.53/0.74      inference('split', [status(esa)], ['9'])).
% 0.53/0.74  thf('61', plain, ($false),
% 0.53/0.74      inference('sat_resolution*', [status(thm)],
% 0.53/0.74                ['1', '23', '24', '41', '59', '60'])).
% 0.53/0.74  
% 0.53/0.74  % SZS output end Refutation
% 0.53/0.74  
% 0.53/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

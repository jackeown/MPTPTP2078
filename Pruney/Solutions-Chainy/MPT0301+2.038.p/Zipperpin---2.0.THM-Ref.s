%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rZhoxQEk1V

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 135 expanded)
%              Number of leaves         :   24 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :  681 (1163 expanded)
%              Number of equality atoms :  107 ( 218 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

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
    ! [X38: $i,X39: $i,X42: $i] :
      ( ( X42
        = ( k2_zfmisc_1 @ X39 @ X38 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X42 @ X38 @ X39 ) @ ( sk_E @ X42 @ X38 @ X39 ) @ ( sk_D @ X42 @ X38 @ X39 ) @ X38 @ X39 )
      | ( r2_hidden @ ( sk_D @ X42 @ X38 @ X39 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X30 @ X32 )
      | ~ ( zip_tseitin_0 @ X30 @ X29 @ X31 @ X32 @ X33 ) ) ),
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
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('6',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X50 @ X51 ) @ X52 )
      | ~ ( r2_hidden @ X50 @ X52 ) ) ),
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
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('12',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X50 @ X51 ) @ X52 )
      | ~ ( r2_hidden @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('14',plain,
    ( ! [X1: $i] :
        ~ ( r2_hidden @ X1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( sk_B_1
        = ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('22',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('25',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('28',plain,(
    ! [X45: $i,X46: $i,X47: $i,X49: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X45 @ X47 ) @ ( k2_zfmisc_1 @ X46 @ X49 ) )
      | ~ ( r2_hidden @ X47 @ X49 )
      | ~ ( r2_hidden @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('33',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('38',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('41',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X41 @ X40 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X41 @ X38 @ X39 ) @ ( sk_E_1 @ X41 @ X38 @ X39 ) @ X41 @ X38 @ X39 )
      | ( X40
       != ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('42',plain,(
    ! [X38: $i,X39: $i,X41: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X41 @ X38 @ X39 ) @ ( sk_E_1 @ X41 @ X38 @ X39 ) @ X41 @ X38 @ X39 )
      | ~ ( r2_hidden @ X41 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X29 @ X33 )
      | ~ ( zip_tseitin_0 @ X30 @ X29 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('47',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('48',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X50 @ X51 ) @ X52 )
      | ~ ( r2_hidden @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('50',plain,
    ( ! [X1: $i] :
        ~ ( r2_hidden @ X1 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('55',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('57',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('60',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','39','58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rZhoxQEk1V
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 152 iterations in 0.076s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.53  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.21/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.53  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.21/0.53  thf(t113_zfmisc_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i]:
% 0.21/0.53        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.53          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      ((((sk_B_1) != (k1_xboole_0))
% 0.21/0.53        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.21/0.53       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf(d2_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.21/0.53       ( ![D:$i]:
% 0.21/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.53           ( ?[E:$i,F:$i]:
% 0.21/0.53             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.53               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_2, axiom,
% 0.21/0.53    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.21/0.53       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.53         ( r2_hidden @ E @ A ) ) ))).
% 0.21/0.53  thf(zf_stmt_3, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.21/0.53       ( ![D:$i]:
% 0.21/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.53           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X38 : $i, X39 : $i, X42 : $i]:
% 0.21/0.53         (((X42) = (k2_zfmisc_1 @ X39 @ X38))
% 0.21/0.53          | (zip_tseitin_0 @ (sk_F @ X42 @ X38 @ X39) @ 
% 0.21/0.53             (sk_E @ X42 @ X38 @ X39) @ (sk_D @ X42 @ X38 @ X39) @ X38 @ X39)
% 0.21/0.53          | (r2_hidden @ (sk_D @ X42 @ X38 @ X39) @ X42))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.53         ((r2_hidden @ X30 @ X32)
% 0.21/0.53          | ~ (zip_tseitin_0 @ X30 @ X29 @ X31 @ X32 @ X33))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.21/0.53          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.21/0.53          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.53  thf('5', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.53  thf(t55_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ (k2_tarski @ X50 @ X51) @ X52)
% 0.21/0.53          | ~ (r2_hidden @ X50 @ X52))),
% 0.21/0.53      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.21/0.53  thf('7', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.21/0.53          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      ((((sk_B_1) = (k1_xboole_0))
% 0.21/0.53        | ((sk_A) = (k1_xboole_0))
% 0.21/0.53        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['9'])).
% 0.21/0.53  thf('11', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_B_1))
% 0.21/0.53         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ (k2_tarski @ X50 @ X51) @ X52)
% 0.21/0.53          | ~ (r2_hidden @ X50 @ X52))),
% 0.21/0.53      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      ((![X1 : $i]: ~ (r2_hidden @ X1 @ sk_B_1))
% 0.21/0.53         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.21/0.53         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['9'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      ((![X0 : $i]: ((sk_B_1) = (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.21/0.53         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      ((((sk_A) != (k1_xboole_0))
% 0.21/0.53        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.21/0.53         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      ((((sk_B_1) != (k1_xboole_0)))
% 0.21/0.53         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.53             (((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['17', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['9'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      ((((sk_B_1) != (sk_B_1)))
% 0.21/0.53         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.53             (((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.21/0.53       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.21/0.53       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('split', [status(esa)], ['18'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.21/0.53         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['9'])).
% 0.21/0.53  thf(t7_xboole_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.53  thf(l54_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.53       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X45 : $i, X46 : $i, X47 : $i, X49 : $i]:
% 0.21/0.53         ((r2_hidden @ (k4_tarski @ X45 @ X47) @ (k2_zfmisc_1 @ X46 @ X49))
% 0.21/0.53          | ~ (r2_hidden @ X47 @ X49)
% 0.21/0.53          | ~ (r2_hidden @ X45 @ X46))),
% 0.21/0.53      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (((X0) = (k1_xboole_0))
% 0.21/0.53          | ~ (r2_hidden @ X2 @ X1)
% 0.21/0.53          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.21/0.53             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((X0) = (k1_xboole_0))
% 0.21/0.53          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 0.21/0.53             (k2_zfmisc_1 @ X0 @ X1))
% 0.21/0.53          | ((X1) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['26', '29'])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.53          k1_xboole_0)
% 0.21/0.53         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.53         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.53         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['25', '30'])).
% 0.21/0.53  thf('32', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.21/0.53         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (((((sk_B_1) != (sk_B_1)) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.53         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.53             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.53         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.53             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['18'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      ((((sk_A) != (sk_A)))
% 0.21/0.53         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.53             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.21/0.53             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      ((((sk_A) = (k1_xboole_0))) | 
% 0.21/0.53       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.21/0.53       (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X41 @ X40)
% 0.21/0.53          | (zip_tseitin_0 @ (sk_F_1 @ X41 @ X38 @ X39) @ 
% 0.21/0.53             (sk_E_1 @ X41 @ X38 @ X39) @ X41 @ X38 @ X39)
% 0.21/0.53          | ((X40) != (k2_zfmisc_1 @ X39 @ X38)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X38 : $i, X39 : $i, X41 : $i]:
% 0.21/0.53         ((zip_tseitin_0 @ (sk_F_1 @ X41 @ X38 @ X39) @ 
% 0.21/0.53           (sk_E_1 @ X41 @ X38 @ X39) @ X41 @ X38 @ X39)
% 0.21/0.53          | ~ (r2_hidden @ X41 @ (k2_zfmisc_1 @ X39 @ X38)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.21/0.53          | (zip_tseitin_0 @ 
% 0.21/0.53             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.21/0.53             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.21/0.53             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['40', '42'])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.53         ((r2_hidden @ X29 @ X33)
% 0.21/0.53          | ~ (zip_tseitin_0 @ X30 @ X29 @ X31 @ X32 @ X33))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 0.21/0.53          | (r2_hidden @ 
% 0.21/0.53             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['9'])).
% 0.21/0.53  thf('47', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['46', '47'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ (k2_tarski @ X50 @ X51) @ X52)
% 0.21/0.53          | ~ (r2_hidden @ X50 @ X52))),
% 0.21/0.53      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      ((![X1 : $i]: ~ (r2_hidden @ X1 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (k1_xboole_0)))
% 0.21/0.53         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['45', '50'])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['9'])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (sk_A)))
% 0.21/0.53         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.53      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.21/0.53         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['18'])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      ((((sk_A) != (k1_xboole_0)))
% 0.21/0.53         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.53             (((sk_A) = (k1_xboole_0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['9'])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      ((((sk_A) != (sk_A)))
% 0.21/0.53         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.53             (((sk_A) = (k1_xboole_0))))),
% 0.21/0.53      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.21/0.53       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.53  thf('59', plain,
% 0.21/0.53      ((((sk_A) = (k1_xboole_0))) | 
% 0.21/0.53       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.21/0.53       (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('split', [status(esa)], ['9'])).
% 0.21/0.53  thf('60', plain, ($false),
% 0.21/0.53      inference('sat_resolution*', [status(thm)],
% 0.21/0.53                ['1', '23', '24', '39', '58', '59'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TzzRtPvYqM

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:02 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  122 (3476 expanded)
%              Number of leaves         :   25 ( 947 expanded)
%              Depth                    :   24
%              Number of atoms          :  893 (33235 expanded)
%              Number of equality atoms :  153 (6149 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('2',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('4',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X33 @ X34 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('5',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X33: $i,X35: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X33 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('8',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('12',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C_1 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ ( k2_mcart_1 @ sk_A ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','12'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('14',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( r2_hidden @ X38 @ X36 )
      | ( ( sk_B @ X36 )
       != ( k4_tarski @ X38 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X36: $i] :
      ( ( X36 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X36 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('18',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('19',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X16 )
      | ~ ( r2_hidden @ X11 @ X16 )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ( X13
       != ( k4_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('25',plain,(
    ! [X11: $i,X12: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X11 @ X16 )
      | ( zip_tseitin_0 @ X12 @ X11 @ ( k4_tarski @ X11 @ X12 ) @ X14 @ X16 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ X2 @ ( k4_tarski @ X2 @ X0 ) @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ X0 @ X1 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X19 @ X22 )
      | ( X22
       != ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X21 @ X20 ) )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','30'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_zfmisc_1 @ X28 @ X29 )
        = k1_xboole_0 )
      | ( X28 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('33',plain,(
    ! [X29: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X29 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('36',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('37',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('38',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['6','7'])).

thf('39',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_A
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( r2_hidden @ X37 @ X36 )
      | ( ( sk_B @ X36 )
       != ( k4_tarski @ X38 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('45',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('46',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X31 != X30 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X31 ) @ ( k1_tarski @ X30 ) )
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('47',plain,(
    ! [X30: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X30 ) )
     != ( k1_tarski @ X30 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('50',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('51',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X29: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X29 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('58',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( X0 = sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( k4_tarski @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X33: $i,X35: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X33 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( k2_mcart_1 @ sk_A )
        = X0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('64',plain,
    ( ! [X0: $i] : ( sk_A = X0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ! [X0: $i] : ( sk_A = X0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('66',plain,
    ( ! [X0: $i] : ( sk_A = X0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('67',plain,
    ( ! [X0: $i] : ( sk_A = X0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('68',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','64','65','66','67'])).

thf('69',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('71',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['34','71'])).

thf('73',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','20'])).

thf('74',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( X0 = sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_tarski @ sk_A @ X0 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X33: $i,X35: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X33 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k2_mcart_1 @ sk_A )
      = X0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','20'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('82',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('83',plain,(
    ! [X30: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X30 ) )
     != ( k1_tarski @ X30 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('87',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','20'])).

thf('88',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','20'])).

thf('89',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('91',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_mcart_1 @ sk_A )
      = X0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('93',plain,(
    ( k2_mcart_1 @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] : ( X0 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','93'])).

thf('95',plain,(
    $false ),
    inference(simplify,[status(thm)],['94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TzzRtPvYqM
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:03:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.62  % Solved by: fo/fo7.sh
% 0.45/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.62  % done 327 iterations in 0.189s
% 0.45/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.62  % SZS output start Refutation
% 0.45/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.62  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.45/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.62  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.45/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.45/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.62  thf(d1_tarski, axiom,
% 0.45/0.62    (![A:$i,B:$i]:
% 0.45/0.62     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.45/0.62  thf('0', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.62         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.45/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.62  thf('1', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.62      inference('simplify', [status(thm)], ['0'])).
% 0.45/0.62  thf(t20_mcart_1, conjecture,
% 0.45/0.62    (![A:$i]:
% 0.45/0.62     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.45/0.62       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.45/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.62    (~( ![A:$i]:
% 0.45/0.62        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.45/0.62          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.45/0.62    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.45/0.62  thf('2', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('3', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf(t7_mcart_1, axiom,
% 0.45/0.62    (![A:$i,B:$i]:
% 0.45/0.62     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.45/0.62       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.45/0.62  thf('4', plain,
% 0.45/0.62      (![X33 : $i, X34 : $i]: ((k1_mcart_1 @ (k4_tarski @ X33 @ X34)) = (X33))),
% 0.45/0.62      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.45/0.62  thf('5', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.45/0.62      inference('sup+', [status(thm)], ['3', '4'])).
% 0.45/0.62  thf('6', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_1))),
% 0.45/0.62      inference('demod', [status(thm)], ['2', '5'])).
% 0.45/0.62  thf('7', plain,
% 0.45/0.62      (![X33 : $i, X35 : $i]: ((k2_mcart_1 @ (k4_tarski @ X33 @ X35)) = (X35))),
% 0.45/0.62      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.45/0.62  thf('8', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 0.45/0.62      inference('sup+', [status(thm)], ['6', '7'])).
% 0.45/0.62  thf('9', plain,
% 0.45/0.62      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('10', plain,
% 0.45/0.62      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('split', [status(esa)], ['9'])).
% 0.45/0.62  thf('11', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_1))),
% 0.45/0.62      inference('demod', [status(thm)], ['2', '5'])).
% 0.45/0.62  thf('12', plain,
% 0.45/0.62      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_1)))
% 0.45/0.62         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('sup+', [status(thm)], ['10', '11'])).
% 0.45/0.62  thf('13', plain,
% 0.45/0.62      ((((sk_A) = (k4_tarski @ sk_A @ (k2_mcart_1 @ sk_A))))
% 0.45/0.62         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('sup+', [status(thm)], ['8', '12'])).
% 0.45/0.62  thf(t9_mcart_1, axiom,
% 0.45/0.62    (![A:$i]:
% 0.45/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.62          ( ![B:$i]:
% 0.45/0.62            ( ~( ( r2_hidden @ B @ A ) & 
% 0.45/0.62                 ( ![C:$i,D:$i]:
% 0.45/0.62                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.45/0.62                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.62  thf('14', plain,
% 0.45/0.62      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.45/0.62         (((X36) = (k1_xboole_0))
% 0.45/0.62          | ~ (r2_hidden @ X38 @ X36)
% 0.45/0.62          | ((sk_B @ X36) != (k4_tarski @ X38 @ X37)))),
% 0.45/0.62      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.45/0.62  thf('15', plain,
% 0.45/0.62      ((![X0 : $i]:
% 0.45/0.62          (((sk_B @ X0) != (sk_A))
% 0.45/0.62           | ~ (r2_hidden @ sk_A @ X0)
% 0.45/0.62           | ((X0) = (k1_xboole_0))))
% 0.45/0.62         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.62  thf('16', plain,
% 0.45/0.62      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.45/0.62         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.45/0.62         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('sup-', [status(thm)], ['1', '15'])).
% 0.45/0.62  thf('17', plain,
% 0.45/0.62      (![X36 : $i]:
% 0.45/0.62         (((X36) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X36) @ X36))),
% 0.45/0.62      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.45/0.62  thf('18', plain,
% 0.45/0.62      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.45/0.62         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.45/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.62  thf('19', plain,
% 0.45/0.62      (![X0 : $i, X3 : $i]:
% 0.45/0.62         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.45/0.62      inference('simplify', [status(thm)], ['18'])).
% 0.45/0.62  thf('20', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.45/0.62          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.45/0.62      inference('sup-', [status(thm)], ['17', '19'])).
% 0.45/0.62  thf('21', plain,
% 0.45/0.62      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.45/0.62         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('clc', [status(thm)], ['16', '20'])).
% 0.45/0.62  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.62      inference('simplify', [status(thm)], ['0'])).
% 0.45/0.62  thf('23', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.62      inference('simplify', [status(thm)], ['0'])).
% 0.45/0.62  thf(d2_zfmisc_1, axiom,
% 0.45/0.62    (![A:$i,B:$i,C:$i]:
% 0.45/0.62     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.45/0.62       ( ![D:$i]:
% 0.45/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.62           ( ?[E:$i,F:$i]:
% 0.45/0.62             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.45/0.62               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.45/0.62  thf(zf_stmt_1, axiom,
% 0.45/0.62    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.45/0.62     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.45/0.62       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.45/0.62         ( r2_hidden @ E @ A ) ) ))).
% 0.45/0.62  thf('24', plain,
% 0.45/0.62      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.45/0.62         ((zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X16)
% 0.45/0.62          | ~ (r2_hidden @ X11 @ X16)
% 0.45/0.62          | ~ (r2_hidden @ X12 @ X14)
% 0.45/0.62          | ((X13) != (k4_tarski @ X11 @ X12)))),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.62  thf('25', plain,
% 0.45/0.62      (![X11 : $i, X12 : $i, X14 : $i, X16 : $i]:
% 0.45/0.62         (~ (r2_hidden @ X12 @ X14)
% 0.45/0.62          | ~ (r2_hidden @ X11 @ X16)
% 0.45/0.62          | (zip_tseitin_0 @ X12 @ X11 @ (k4_tarski @ X11 @ X12) @ X14 @ X16))),
% 0.45/0.62      inference('simplify', [status(thm)], ['24'])).
% 0.45/0.62  thf('26', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.62         ((zip_tseitin_0 @ X0 @ X2 @ (k4_tarski @ X2 @ X0) @ 
% 0.45/0.62           (k1_tarski @ X0) @ X1)
% 0.45/0.62          | ~ (r2_hidden @ X2 @ X1))),
% 0.45/0.62      inference('sup-', [status(thm)], ['23', '25'])).
% 0.45/0.62  thf('27', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         (zip_tseitin_0 @ X1 @ X0 @ (k4_tarski @ X0 @ X1) @ (k1_tarski @ X1) @ 
% 0.45/0.62          (k1_tarski @ X0))),
% 0.45/0.62      inference('sup-', [status(thm)], ['22', '26'])).
% 0.45/0.62  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.45/0.62  thf(zf_stmt_3, axiom,
% 0.45/0.62    (![A:$i,B:$i,C:$i]:
% 0.45/0.62     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.45/0.62       ( ![D:$i]:
% 0.45/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.62           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.45/0.62  thf('28', plain,
% 0.45/0.62      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.62         (~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.45/0.62          | (r2_hidden @ X19 @ X22)
% 0.45/0.62          | ((X22) != (k2_zfmisc_1 @ X21 @ X20)))),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.62  thf('29', plain,
% 0.45/0.62      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.62         ((r2_hidden @ X19 @ (k2_zfmisc_1 @ X21 @ X20))
% 0.45/0.62          | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 0.45/0.62      inference('simplify', [status(thm)], ['28'])).
% 0.45/0.62  thf('30', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.45/0.62          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.45/0.62      inference('sup-', [status(thm)], ['27', '29'])).
% 0.45/0.62  thf('31', plain,
% 0.45/0.62      ((![X0 : $i]:
% 0.45/0.62          (r2_hidden @ (k4_tarski @ sk_A @ X0) @ 
% 0.45/0.62           (k2_zfmisc_1 @ k1_xboole_0 @ (k1_tarski @ X0))))
% 0.45/0.62         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('sup+', [status(thm)], ['21', '30'])).
% 0.45/0.62  thf(t113_zfmisc_1, axiom,
% 0.45/0.62    (![A:$i,B:$i]:
% 0.45/0.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.62  thf('32', plain,
% 0.45/0.62      (![X28 : $i, X29 : $i]:
% 0.45/0.62         (((k2_zfmisc_1 @ X28 @ X29) = (k1_xboole_0))
% 0.45/0.62          | ((X28) != (k1_xboole_0)))),
% 0.45/0.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.45/0.62  thf('33', plain,
% 0.45/0.62      (![X29 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X29) = (k1_xboole_0))),
% 0.45/0.62      inference('simplify', [status(thm)], ['32'])).
% 0.45/0.62  thf('34', plain,
% 0.45/0.62      ((![X0 : $i]: (r2_hidden @ (k4_tarski @ sk_A @ X0) @ k1_xboole_0))
% 0.45/0.62         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('demod', [status(thm)], ['31', '33'])).
% 0.45/0.62  thf('35', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.62      inference('simplify', [status(thm)], ['0'])).
% 0.45/0.62  thf('36', plain,
% 0.45/0.62      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('split', [status(esa)], ['9'])).
% 0.45/0.62  thf('37', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_1))),
% 0.45/0.62      inference('demod', [status(thm)], ['2', '5'])).
% 0.45/0.62  thf('38', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 0.45/0.62      inference('sup+', [status(thm)], ['6', '7'])).
% 0.45/0.62  thf('39', plain,
% 0.45/0.62      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 0.45/0.62      inference('demod', [status(thm)], ['37', '38'])).
% 0.45/0.62  thf('40', plain,
% 0.45/0.62      ((((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_A)))
% 0.45/0.62         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('sup+', [status(thm)], ['36', '39'])).
% 0.45/0.62  thf('41', plain,
% 0.45/0.62      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.45/0.62         (((X36) = (k1_xboole_0))
% 0.45/0.62          | ~ (r2_hidden @ X37 @ X36)
% 0.45/0.62          | ((sk_B @ X36) != (k4_tarski @ X38 @ X37)))),
% 0.45/0.62      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.45/0.62  thf('42', plain,
% 0.45/0.62      ((![X0 : $i]:
% 0.45/0.62          (((sk_B @ X0) != (sk_A))
% 0.45/0.62           | ~ (r2_hidden @ sk_A @ X0)
% 0.45/0.62           | ((X0) = (k1_xboole_0))))
% 0.45/0.62         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.62  thf('43', plain,
% 0.45/0.62      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.45/0.62         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.45/0.62         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('sup-', [status(thm)], ['35', '42'])).
% 0.45/0.62  thf('44', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.45/0.62          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.45/0.62      inference('sup-', [status(thm)], ['17', '19'])).
% 0.45/0.62  thf('45', plain,
% 0.45/0.62      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.45/0.62         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('clc', [status(thm)], ['43', '44'])).
% 0.45/0.62  thf(t20_zfmisc_1, axiom,
% 0.45/0.62    (![A:$i,B:$i]:
% 0.45/0.62     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.45/0.62         ( k1_tarski @ A ) ) <=>
% 0.45/0.62       ( ( A ) != ( B ) ) ))).
% 0.45/0.62  thf('46', plain,
% 0.45/0.62      (![X30 : $i, X31 : $i]:
% 0.45/0.62         (((X31) != (X30))
% 0.45/0.62          | ((k4_xboole_0 @ (k1_tarski @ X31) @ (k1_tarski @ X30))
% 0.45/0.62              != (k1_tarski @ X31)))),
% 0.45/0.62      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.45/0.62  thf('47', plain,
% 0.45/0.62      (![X30 : $i]:
% 0.45/0.62         ((k4_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X30))
% 0.45/0.62           != (k1_tarski @ X30))),
% 0.45/0.62      inference('simplify', [status(thm)], ['46'])).
% 0.45/0.62  thf('48', plain,
% 0.45/0.62      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) != (k1_tarski @ sk_A)))
% 0.45/0.62         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('sup-', [status(thm)], ['45', '47'])).
% 0.45/0.62  thf('49', plain,
% 0.45/0.62      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.45/0.62         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('clc', [status(thm)], ['43', '44'])).
% 0.45/0.62  thf('50', plain,
% 0.45/0.62      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.45/0.62         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('clc', [status(thm)], ['43', '44'])).
% 0.45/0.62  thf('51', plain,
% 0.45/0.62      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.45/0.62         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.45/0.62  thf('52', plain,
% 0.45/0.62      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.45/0.62         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('clc', [status(thm)], ['43', '44'])).
% 0.45/0.62  thf('53', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.45/0.62          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.45/0.62      inference('sup-', [status(thm)], ['27', '29'])).
% 0.45/0.62  thf('54', plain,
% 0.45/0.62      ((![X0 : $i]:
% 0.45/0.62          (r2_hidden @ (k4_tarski @ sk_A @ X0) @ 
% 0.45/0.62           (k2_zfmisc_1 @ k1_xboole_0 @ (k1_tarski @ X0))))
% 0.45/0.62         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('sup+', [status(thm)], ['52', '53'])).
% 0.45/0.62  thf('55', plain,
% 0.45/0.62      (![X29 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X29) = (k1_xboole_0))),
% 0.45/0.62      inference('simplify', [status(thm)], ['32'])).
% 0.45/0.62  thf('56', plain,
% 0.45/0.62      ((![X0 : $i]: (r2_hidden @ (k4_tarski @ sk_A @ X0) @ k1_xboole_0))
% 0.45/0.62         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('demod', [status(thm)], ['54', '55'])).
% 0.45/0.62  thf('57', plain,
% 0.45/0.62      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.45/0.62         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('clc', [status(thm)], ['43', '44'])).
% 0.45/0.62  thf('58', plain,
% 0.45/0.62      (![X0 : $i, X3 : $i]:
% 0.45/0.62         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.45/0.62      inference('simplify', [status(thm)], ['18'])).
% 0.45/0.62  thf('59', plain,
% 0.45/0.62      ((![X0 : $i]: (~ (r2_hidden @ X0 @ k1_xboole_0) | ((X0) = (sk_A))))
% 0.45/0.62         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.62  thf('60', plain,
% 0.45/0.62      ((![X0 : $i]: ((k4_tarski @ sk_A @ X0) = (sk_A)))
% 0.45/0.62         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('sup-', [status(thm)], ['56', '59'])).
% 0.45/0.62  thf('61', plain,
% 0.45/0.62      (![X33 : $i, X35 : $i]: ((k2_mcart_1 @ (k4_tarski @ X33 @ X35)) = (X35))),
% 0.45/0.62      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.45/0.62  thf('62', plain,
% 0.45/0.62      ((![X0 : $i]: ((k2_mcart_1 @ sk_A) = (X0)))
% 0.45/0.62         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('sup+', [status(thm)], ['60', '61'])).
% 0.45/0.62  thf('63', plain,
% 0.45/0.62      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('split', [status(esa)], ['9'])).
% 0.45/0.62  thf('64', plain,
% 0.45/0.62      ((![X0 : $i]: ((sk_A) = (X0))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('demod', [status(thm)], ['62', '63'])).
% 0.45/0.62  thf('65', plain,
% 0.45/0.62      ((![X0 : $i]: ((sk_A) = (X0))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('demod', [status(thm)], ['62', '63'])).
% 0.45/0.62  thf('66', plain,
% 0.45/0.62      ((![X0 : $i]: ((sk_A) = (X0))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('demod', [status(thm)], ['62', '63'])).
% 0.45/0.62  thf('67', plain,
% 0.45/0.62      ((![X0 : $i]: ((sk_A) = (X0))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('demod', [status(thm)], ['62', '63'])).
% 0.45/0.62  thf('68', plain,
% 0.45/0.62      ((((sk_A) != (sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('demod', [status(thm)], ['51', '64', '65', '66', '67'])).
% 0.45/0.62  thf('69', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.45/0.62      inference('simplify', [status(thm)], ['68'])).
% 0.45/0.62  thf('70', plain,
% 0.45/0.62      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.45/0.62      inference('split', [status(esa)], ['9'])).
% 0.45/0.62  thf('71', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.45/0.62      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 0.45/0.62  thf('72', plain,
% 0.45/0.62      (![X0 : $i]: (r2_hidden @ (k4_tarski @ sk_A @ X0) @ k1_xboole_0)),
% 0.45/0.62      inference('simpl_trail', [status(thm)], ['34', '71'])).
% 0.45/0.62  thf('73', plain,
% 0.45/0.62      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.45/0.62         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('clc', [status(thm)], ['16', '20'])).
% 0.45/0.62  thf('74', plain,
% 0.45/0.62      (![X0 : $i, X3 : $i]:
% 0.45/0.62         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.45/0.62      inference('simplify', [status(thm)], ['18'])).
% 0.45/0.62  thf('75', plain,
% 0.45/0.62      ((![X0 : $i]: (~ (r2_hidden @ X0 @ k1_xboole_0) | ((X0) = (sk_A))))
% 0.45/0.62         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('sup-', [status(thm)], ['73', '74'])).
% 0.45/0.62  thf('76', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.45/0.62      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 0.45/0.62  thf('77', plain,
% 0.45/0.62      (![X0 : $i]: (~ (r2_hidden @ X0 @ k1_xboole_0) | ((X0) = (sk_A)))),
% 0.45/0.62      inference('simpl_trail', [status(thm)], ['75', '76'])).
% 0.45/0.62  thf('78', plain, (![X0 : $i]: ((k4_tarski @ sk_A @ X0) = (sk_A))),
% 0.45/0.62      inference('sup-', [status(thm)], ['72', '77'])).
% 0.45/0.62  thf('79', plain,
% 0.45/0.62      (![X33 : $i, X35 : $i]: ((k2_mcart_1 @ (k4_tarski @ X33 @ X35)) = (X35))),
% 0.45/0.62      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.45/0.62  thf('80', plain, (![X0 : $i]: ((k2_mcart_1 @ sk_A) = (X0))),
% 0.45/0.62      inference('sup+', [status(thm)], ['78', '79'])).
% 0.45/0.62  thf('81', plain,
% 0.45/0.62      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.45/0.62         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('clc', [status(thm)], ['16', '20'])).
% 0.45/0.62  thf(t69_enumset1, axiom,
% 0.45/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.62  thf('82', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.45/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.62  thf('83', plain,
% 0.45/0.62      (![X30 : $i]:
% 0.45/0.62         ((k4_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X30))
% 0.45/0.62           != (k1_tarski @ X30))),
% 0.45/0.62      inference('simplify', [status(thm)], ['46'])).
% 0.45/0.62  thf('84', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 0.45/0.62           != (k1_tarski @ X0))),
% 0.45/0.62      inference('sup-', [status(thm)], ['82', '83'])).
% 0.45/0.62  thf('85', plain,
% 0.45/0.62      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ k1_xboole_0)
% 0.45/0.62          != (k1_tarski @ sk_A)))
% 0.45/0.62         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('sup-', [status(thm)], ['81', '84'])).
% 0.45/0.62  thf('86', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.45/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.62  thf('87', plain,
% 0.45/0.62      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.45/0.62         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('clc', [status(thm)], ['16', '20'])).
% 0.45/0.62  thf('88', plain,
% 0.45/0.62      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.45/0.62         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('clc', [status(thm)], ['16', '20'])).
% 0.45/0.62  thf('89', plain,
% 0.45/0.62      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.45/0.62         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.62      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.45/0.62  thf('90', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.45/0.62      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 0.45/0.62  thf('91', plain,
% 0.45/0.62      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.45/0.62      inference('simpl_trail', [status(thm)], ['89', '90'])).
% 0.45/0.62  thf('92', plain, (![X0 : $i]: ((k2_mcart_1 @ sk_A) = (X0))),
% 0.45/0.62      inference('sup+', [status(thm)], ['78', '79'])).
% 0.45/0.62  thf('93', plain, (((k2_mcart_1 @ sk_A) != (k1_xboole_0))),
% 0.45/0.62      inference('demod', [status(thm)], ['91', '92'])).
% 0.45/0.62  thf('94', plain, (![X0 : $i]: ((X0) != (k1_xboole_0))),
% 0.45/0.62      inference('sup-', [status(thm)], ['80', '93'])).
% 0.45/0.62  thf('95', plain, ($false), inference('simplify', [status(thm)], ['94'])).
% 0.45/0.62  
% 0.45/0.62  % SZS output end Refutation
% 0.45/0.62  
% 0.45/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

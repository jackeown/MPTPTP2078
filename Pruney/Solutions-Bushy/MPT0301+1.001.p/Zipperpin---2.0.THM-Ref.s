%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0301+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G4cLg9J4ll

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:40 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 133 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  672 (1101 expanded)
%              Number of equality atoms :   98 ( 182 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('4',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('5',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('7',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ( X11
       != ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('12',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

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
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','21'])).

thf('23',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('24',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('25',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('26',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X5 )
      | ~ ( r2_hidden @ X0 @ X5 )
      | ~ ( r2_hidden @ X1 @ X3 )
      | ( X2
       != ( k4_tarski @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X3: $i,X5: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X0 @ X5 )
      | ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ X0 @ X1 ) @ X3 @ X5 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_B @ X0 ) @ X2 @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_B @ X1 ) @ ( sk_B @ X0 ) @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ X1 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 )
      | ( r2_hidden @ X8 @ X11 )
      | ( X11
       != ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X10 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['4','7'])).

thf('38',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('43',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('46',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( sk_A = X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_A = o_0_0_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X0 @ X4 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('58',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','59'])).

thf('61',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('62',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','22','23','44','60','61'])).


%------------------------------------------------------------------------------

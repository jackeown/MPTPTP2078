%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LBeBR6UgFA

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:00 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 119 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  662 (1021 expanded)
%              Number of equality atoms :   92 ( 168 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('4',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

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
    ! [X13: $i,X14: $i,X17: $i] :
      ( ( X17
        = ( k2_zfmisc_1 @ X14 @ X13 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X17 @ X13 @ X14 ) @ ( sk_E @ X17 @ X13 @ X14 ) @ ( sk_D @ X17 @ X13 @ X14 ) @ X13 @ X14 )
      | ( r2_hidden @ ( sk_D @ X17 @ X13 @ X14 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ X7 )
      | ~ ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ sk_B_2 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,
    ( ~ ( v1_xboole_0 @ sk_B_2 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('21',plain,
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

thf('22',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('23',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X9 )
      | ~ ( r2_hidden @ X4 @ X9 )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ( X6
       != ( k4_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,(
    ! [X4: $i,X5: $i,X7: $i,X9: $i] :
      ( ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r2_hidden @ X4 @ X9 )
      | ( zip_tseitin_0 @ X5 @ X4 @ ( k4_tarski @ X4 @ X5 ) @ X7 @ X9 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_B_1 @ X0 ) @ X2 @ ( k4_tarski @ X2 @ ( sk_B_1 @ X0 ) ) @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_B_1 @ X1 ) @ ( sk_B_1 @ X0 ) @ ( k4_tarski @ ( sk_B_1 @ X0 ) @ ( sk_B_1 @ X1 ) ) @ X1 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 @ X14 )
      | ( r2_hidden @ X12 @ X15 )
      | ( X15
       != ( k2_zfmisc_1 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X14 @ X13 ) )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X0 ) @ ( sk_B_1 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('35',plain,
    ( ( ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( ( sk_B_2 != sk_B_2 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('40',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ( X17
        = ( k2_zfmisc_1 @ X14 @ X13 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X17 @ X13 @ X14 ) @ ( sk_E @ X17 @ X13 @ X14 ) @ ( sk_D @ X17 @ X13 @ X14 ) @ X13 @ X14 )
      | ( r2_hidden @ ( sk_D @ X17 @ X13 @ X14 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X4 @ X8 )
      | ~ ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ sk_A )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('56',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','56'])).

thf('58',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('59',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','19','20','41','57','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LBeBR6UgFA
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:20:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.62  % Solved by: fo/fo7.sh
% 0.44/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.62  % done 324 iterations in 0.168s
% 0.44/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.62  % SZS output start Refutation
% 0.44/0.62  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.44/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.44/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.62  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.44/0.62  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.44/0.62  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.44/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.44/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.44/0.62  thf(t113_zfmisc_1, conjecture,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.44/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.44/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.62    (~( ![A:$i,B:$i]:
% 0.44/0.62        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.44/0.62          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.44/0.62    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.44/0.62  thf('0', plain,
% 0.44/0.62      ((((sk_B_2) != (k1_xboole_0))
% 0.44/0.62        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) != (k1_xboole_0)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('1', plain,
% 0.44/0.62      (~ (((sk_B_2) = (k1_xboole_0))) | 
% 0.44/0.62       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.44/0.62      inference('split', [status(esa)], ['0'])).
% 0.44/0.62  thf('2', plain,
% 0.44/0.62      ((((sk_B_2) = (k1_xboole_0))
% 0.44/0.62        | ((sk_A) = (k1_xboole_0))
% 0.44/0.62        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('3', plain,
% 0.44/0.62      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.44/0.62      inference('split', [status(esa)], ['2'])).
% 0.44/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.44/0.62  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.62  thf('5', plain, (((v1_xboole_0 @ sk_B_2)) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.44/0.62      inference('sup+', [status(thm)], ['3', '4'])).
% 0.44/0.62  thf(d2_zfmisc_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.44/0.62       ( ![D:$i]:
% 0.44/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.44/0.62           ( ?[E:$i,F:$i]:
% 0.44/0.62             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.44/0.62               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.44/0.62  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.44/0.62  thf(zf_stmt_2, axiom,
% 0.44/0.62    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.44/0.62     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.44/0.62       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.44/0.62         ( r2_hidden @ E @ A ) ) ))).
% 0.44/0.62  thf(zf_stmt_3, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.44/0.62       ( ![D:$i]:
% 0.44/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.44/0.62           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.44/0.62  thf('6', plain,
% 0.44/0.62      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.44/0.62         (((X17) = (k2_zfmisc_1 @ X14 @ X13))
% 0.44/0.62          | (zip_tseitin_0 @ (sk_F @ X17 @ X13 @ X14) @ 
% 0.44/0.62             (sk_E @ X17 @ X13 @ X14) @ (sk_D @ X17 @ X13 @ X14) @ X13 @ X14)
% 0.44/0.62          | (r2_hidden @ (sk_D @ X17 @ X13 @ X14) @ X17))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.62  thf('7', plain,
% 0.44/0.62      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.62         ((r2_hidden @ X5 @ X7) | ~ (zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.44/0.62  thf('8', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.44/0.62          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.44/0.62          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.44/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.44/0.62  thf(d1_xboole_0, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.44/0.62  thf('9', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.44/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.44/0.62  thf('10', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 0.44/0.62          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.44/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.62  thf('11', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.44/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.44/0.62  thf('12', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X2)
% 0.44/0.62          | ((X2) = (k2_zfmisc_1 @ X1 @ X0))
% 0.44/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.62  thf('13', plain,
% 0.44/0.62      ((((sk_A) != (k1_xboole_0))
% 0.44/0.62        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) != (k1_xboole_0)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('14', plain,
% 0.44/0.62      ((((k2_zfmisc_1 @ sk_A @ sk_B_2) != (k1_xboole_0)))
% 0.44/0.62         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.44/0.62      inference('split', [status(esa)], ['13'])).
% 0.44/0.62  thf('15', plain,
% 0.44/0.62      ((![X0 : $i]:
% 0.44/0.62          (((X0) != (k1_xboole_0))
% 0.44/0.62           | ~ (v1_xboole_0 @ sk_B_2)
% 0.44/0.62           | ~ (v1_xboole_0 @ X0)))
% 0.44/0.62         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['12', '14'])).
% 0.44/0.62  thf('16', plain,
% 0.44/0.62      (((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_2)))
% 0.44/0.62         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.44/0.62      inference('simplify', [status(thm)], ['15'])).
% 0.44/0.62  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.62  thf('18', plain,
% 0.44/0.62      ((~ (v1_xboole_0 @ sk_B_2))
% 0.44/0.62         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.44/0.62      inference('simplify_reflect+', [status(thm)], ['16', '17'])).
% 0.44/0.62  thf('19', plain,
% 0.44/0.62      (~ (((sk_B_2) = (k1_xboole_0))) | 
% 0.44/0.62       (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['5', '18'])).
% 0.44/0.62  thf('20', plain,
% 0.44/0.62      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.44/0.62       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.44/0.62      inference('split', [status(esa)], ['13'])).
% 0.44/0.62  thf('21', plain,
% 0.44/0.62      ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))
% 0.44/0.62         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.44/0.62      inference('split', [status(esa)], ['2'])).
% 0.44/0.62  thf(t7_xboole_0, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.44/0.62          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.44/0.62  thf('22', plain,
% 0.44/0.62      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.44/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.44/0.62  thf('23', plain,
% 0.44/0.62      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.44/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.44/0.62  thf('24', plain,
% 0.44/0.62      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.44/0.62         ((zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X9)
% 0.44/0.62          | ~ (r2_hidden @ X4 @ X9)
% 0.44/0.62          | ~ (r2_hidden @ X5 @ X7)
% 0.44/0.62          | ((X6) != (k4_tarski @ X4 @ X5)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.44/0.62  thf('25', plain,
% 0.44/0.62      (![X4 : $i, X5 : $i, X7 : $i, X9 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X5 @ X7)
% 0.44/0.62          | ~ (r2_hidden @ X4 @ X9)
% 0.44/0.62          | (zip_tseitin_0 @ X5 @ X4 @ (k4_tarski @ X4 @ X5) @ X7 @ X9))),
% 0.44/0.62      inference('simplify', [status(thm)], ['24'])).
% 0.44/0.62  thf('26', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         (((X0) = (k1_xboole_0))
% 0.44/0.62          | (zip_tseitin_0 @ (sk_B_1 @ X0) @ X2 @ 
% 0.44/0.62             (k4_tarski @ X2 @ (sk_B_1 @ X0)) @ X0 @ X1)
% 0.44/0.62          | ~ (r2_hidden @ X2 @ X1))),
% 0.44/0.62      inference('sup-', [status(thm)], ['23', '25'])).
% 0.44/0.62  thf('27', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (((X0) = (k1_xboole_0))
% 0.44/0.62          | (zip_tseitin_0 @ (sk_B_1 @ X1) @ (sk_B_1 @ X0) @ 
% 0.44/0.62             (k4_tarski @ (sk_B_1 @ X0) @ (sk_B_1 @ X1)) @ X1 @ X0)
% 0.44/0.62          | ((X1) = (k1_xboole_0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['22', '26'])).
% 0.44/0.62  thf('28', plain,
% 0.44/0.62      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.44/0.62         (~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.44/0.62          | (r2_hidden @ X12 @ X15)
% 0.44/0.62          | ((X15) != (k2_zfmisc_1 @ X14 @ X13)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.62  thf('29', plain,
% 0.44/0.62      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.44/0.62         ((r2_hidden @ X12 @ (k2_zfmisc_1 @ X14 @ X13))
% 0.44/0.62          | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 @ X14))),
% 0.44/0.62      inference('simplify', [status(thm)], ['28'])).
% 0.44/0.62  thf('30', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (((X1) = (k1_xboole_0))
% 0.44/0.62          | ((X0) = (k1_xboole_0))
% 0.44/0.62          | (r2_hidden @ (k4_tarski @ (sk_B_1 @ X0) @ (sk_B_1 @ X1)) @ 
% 0.44/0.62             (k2_zfmisc_1 @ X0 @ X1)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['27', '29'])).
% 0.44/0.62  thf('31', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.44/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.44/0.62  thf('32', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (((X1) = (k1_xboole_0))
% 0.44/0.62          | ((X0) = (k1_xboole_0))
% 0.44/0.62          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.44/0.62  thf('33', plain,
% 0.44/0.62      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.44/0.62         | ((sk_B_2) = (k1_xboole_0))
% 0.44/0.62         | ((sk_A) = (k1_xboole_0))))
% 0.44/0.62         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['21', '32'])).
% 0.44/0.62  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.62  thf('35', plain,
% 0.44/0.62      (((((sk_B_2) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.44/0.62         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.44/0.62      inference('demod', [status(thm)], ['33', '34'])).
% 0.44/0.62  thf('36', plain,
% 0.44/0.62      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.44/0.62      inference('split', [status(esa)], ['0'])).
% 0.44/0.62  thf('37', plain,
% 0.44/0.62      (((((sk_B_2) != (sk_B_2)) | ((sk_A) = (k1_xboole_0))))
% 0.44/0.62         <= (~ (((sk_B_2) = (k1_xboole_0))) & 
% 0.44/0.62             (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.44/0.62  thf('38', plain,
% 0.44/0.62      ((((sk_A) = (k1_xboole_0)))
% 0.44/0.62         <= (~ (((sk_B_2) = (k1_xboole_0))) & 
% 0.44/0.62             (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.44/0.62      inference('simplify', [status(thm)], ['37'])).
% 0.44/0.62  thf('39', plain,
% 0.44/0.62      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.44/0.62      inference('split', [status(esa)], ['13'])).
% 0.44/0.62  thf('40', plain,
% 0.44/0.62      ((((sk_A) != (sk_A)))
% 0.44/0.62         <= (~ (((sk_B_2) = (k1_xboole_0))) & 
% 0.44/0.62             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.44/0.62             (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.44/0.62  thf('41', plain,
% 0.44/0.62      ((((sk_A) = (k1_xboole_0))) | 
% 0.44/0.62       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))) | 
% 0.44/0.62       (((sk_B_2) = (k1_xboole_0)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['40'])).
% 0.44/0.62  thf('42', plain,
% 0.44/0.62      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.62      inference('split', [status(esa)], ['2'])).
% 0.44/0.62  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.62  thf('44', plain, (((v1_xboole_0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.62      inference('sup+', [status(thm)], ['42', '43'])).
% 0.44/0.62  thf('45', plain,
% 0.44/0.62      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.44/0.62         (((X17) = (k2_zfmisc_1 @ X14 @ X13))
% 0.44/0.62          | (zip_tseitin_0 @ (sk_F @ X17 @ X13 @ X14) @ 
% 0.44/0.62             (sk_E @ X17 @ X13 @ X14) @ (sk_D @ X17 @ X13 @ X14) @ X13 @ X14)
% 0.44/0.62          | (r2_hidden @ (sk_D @ X17 @ X13 @ X14) @ X17))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.62  thf('46', plain,
% 0.44/0.62      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.62         ((r2_hidden @ X4 @ X8) | ~ (zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.44/0.62  thf('47', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.44/0.62          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.44/0.62          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.44/0.62  thf('48', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.44/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.44/0.62  thf('49', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         ((r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1)
% 0.44/0.62          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.44/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['47', '48'])).
% 0.44/0.62  thf('50', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.44/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.44/0.62  thf('51', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X2)
% 0.44/0.62          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.44/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.44/0.62  thf('52', plain,
% 0.44/0.62      ((((k2_zfmisc_1 @ sk_A @ sk_B_2) != (k1_xboole_0)))
% 0.44/0.62         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.44/0.62      inference('split', [status(esa)], ['13'])).
% 0.44/0.62  thf('53', plain,
% 0.44/0.62      ((![X0 : $i]:
% 0.44/0.62          (((X0) != (k1_xboole_0))
% 0.44/0.62           | ~ (v1_xboole_0 @ sk_A)
% 0.44/0.62           | ~ (v1_xboole_0 @ X0)))
% 0.44/0.62         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['51', '52'])).
% 0.44/0.62  thf('54', plain,
% 0.44/0.62      (((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_A)))
% 0.44/0.62         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.44/0.62      inference('simplify', [status(thm)], ['53'])).
% 0.44/0.62  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.62  thf('56', plain,
% 0.44/0.62      ((~ (v1_xboole_0 @ sk_A))
% 0.44/0.62         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.44/0.62      inference('simplify_reflect+', [status(thm)], ['54', '55'])).
% 0.44/0.62  thf('57', plain,
% 0.44/0.62      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.44/0.62       (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['44', '56'])).
% 0.44/0.62  thf('58', plain,
% 0.44/0.62      ((((sk_A) = (k1_xboole_0))) | 
% 0.44/0.62       (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))) | 
% 0.44/0.62       (((sk_B_2) = (k1_xboole_0)))),
% 0.44/0.62      inference('split', [status(esa)], ['2'])).
% 0.44/0.62  thf('59', plain, ($false),
% 0.44/0.62      inference('sat_resolution*', [status(thm)],
% 0.44/0.62                ['1', '19', '20', '41', '57', '58'])).
% 0.44/0.62  
% 0.44/0.62  % SZS output end Refutation
% 0.44/0.62  
% 0.48/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

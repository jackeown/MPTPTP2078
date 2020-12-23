%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hRpX4gwEvH

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:04 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 323 expanded)
%              Number of leaves         :   25 (  96 expanded)
%              Depth                    :   17
%              Number of atoms          : 1198 (3266 expanded)
%              Number of equality atoms :  164 ( 476 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k4_xboole_0 @ X9 @ X11 )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
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

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X24 @ X21 @ X22 ) @ ( sk_E_1 @ X24 @ X21 @ X22 ) @ X24 @ X21 @ X22 )
      | ( X23
       != ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X24 @ X21 @ X22 ) @ ( sk_E_1 @ X24 @ X21 @ X22 ) @ X24 @ X21 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ X15 )
      | ~ ( zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

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

thf('19',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ sk_B_1 )
        = X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('31',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_B_1 )
        = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ X0 )
        = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ X0 @ X0 ) )
       != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ X0 @ X0 ) )
       != sk_B_1 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_xboole_0 != sk_B_1 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','40'])).

thf('42',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('43',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('46',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('47',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('49',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X17 )
      | ~ ( r2_hidden @ X12 @ X17 )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ( X14
       != ( k4_tarski @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('50',plain,(
    ! [X12: $i,X13: $i,X15: $i,X17: $i] :
      ( ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( r2_hidden @ X12 @ X17 )
      | ( zip_tseitin_0 @ X13 @ X12 @ ( k4_tarski @ X12 @ X13 ) @ X15 @ X17 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ X3 @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_C @ X2 @ X1 ) @ ( sk_B @ X0 ) @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_C @ X2 @ X1 ) ) @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X20 @ X23 )
      | ( X23
       != ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X22 @ X21 ) )
      | ~ ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ sk_B_1 ) ) @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ( r1_xboole_0 @ sk_B_1 @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ sk_B_1 ) ) @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ( r1_xboole_0 @ sk_B_1 @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','55'])).

thf('58',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('59',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_xboole_0 @ sk_B_1 @ X0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 )
        | ~ ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ sk_B_1 ) ) @ X1 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_xboole_0 @ sk_B_1 @ X0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ sk_B_1 ) ) @ X1 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_B_1 @ X0 )
        | ( sk_A = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ( r1_xboole_0 @ sk_B_1 @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','68'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ( r1_xboole_0 @ sk_B_1 @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('72',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('79',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('80',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','79'])).

thf('81',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['78','80'])).

thf('82',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['77','81'])).

thf('83',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('84',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('87',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('88',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ sk_A )
        = X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k4_xboole_0 @ X9 @ X11 )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ( X0 != X0 )
        | ( r1_xboole_0 @ X0 @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('94',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X12 @ X16 )
      | ~ ( zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('97',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','100'])).

thf('102',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('105',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('107',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','44','45','85','86','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hRpX4gwEvH
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:11:29 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 762 iterations in 0.215s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.46/0.66  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.46/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.46/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.66  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(t113_zfmisc_1, conjecture,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i,B:$i]:
% 0.46/0.66        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.66          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      ((((sk_B_1) != (k1_xboole_0))
% 0.46/0.66        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.46/0.66       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.46/0.66      inference('split', [status(esa)], ['0'])).
% 0.46/0.66  thf(t3_boole, axiom,
% 0.46/0.66    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.66  thf('2', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.66  thf(t48_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X7 : $i, X8 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.46/0.66           = (k3_xboole_0 @ X7 @ X8))),
% 0.46/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['2', '3'])).
% 0.46/0.66  thf(t2_boole, axiom,
% 0.46/0.66    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.66  thf('6', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.66  thf('7', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.66  thf(t83_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (![X9 : $i, X11 : $i]:
% 0.46/0.66         ((r1_xboole_0 @ X9 @ X11) | ((k4_xboole_0 @ X9 @ X11) != (X9)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.66  thf('10', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.46/0.66      inference('simplify', [status(thm)], ['9'])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['6', '10'])).
% 0.46/0.66  thf(t7_xboole_0, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.66          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.66  thf(d2_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.46/0.66       ( ![D:$i]:
% 0.46/0.66         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.66           ( ?[E:$i,F:$i]:
% 0.46/0.66             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.46/0.66               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_2, axiom,
% 0.46/0.66    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.46/0.66       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.46/0.66         ( r2_hidden @ E @ A ) ) ))).
% 0.46/0.66  thf(zf_stmt_3, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.46/0.66       ( ![D:$i]:
% 0.46/0.66         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.66           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X24 @ X23)
% 0.46/0.66          | (zip_tseitin_0 @ (sk_F_1 @ X24 @ X21 @ X22) @ 
% 0.46/0.66             (sk_E_1 @ X24 @ X21 @ X22) @ X24 @ X21 @ X22)
% 0.46/0.66          | ((X23) != (k2_zfmisc_1 @ X22 @ X21)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X21 : $i, X22 : $i, X24 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ (sk_F_1 @ X24 @ X21 @ X22) @ 
% 0.46/0.66           (sk_E_1 @ X24 @ X21 @ X22) @ X24 @ X21 @ X22)
% 0.46/0.66          | ~ (r2_hidden @ X24 @ (k2_zfmisc_1 @ X22 @ X21)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['13'])).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.46/0.66          | (zip_tseitin_0 @ 
% 0.46/0.66             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.46/0.66             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.46/0.66             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['12', '14'])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.66         ((r2_hidden @ X13 @ X15)
% 0.46/0.66          | ~ (zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X16))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ 
% 0.46/0.66             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ 
% 0.46/0.66             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.66  thf(t3_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.46/0.66            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.66       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.66            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X2 @ X0)
% 0.46/0.66          | ~ (r2_hidden @ X2 @ X3)
% 0.46/0.66          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.46/0.66          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.46/0.66          | ~ (r2_hidden @ 
% 0.46/0.66               (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ X2))),
% 0.46/0.66      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.46/0.66          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.46/0.66          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['17', '20'])).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r1_xboole_0 @ X0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['21'])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['11', '22'])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      ((((sk_B_1) = (k1_xboole_0))
% 0.46/0.66        | ((sk_A) = (k1_xboole_0))
% 0.46/0.66        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.66      inference('split', [status(esa)], ['24'])).
% 0.46/0.66  thf('26', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_B_1) = (X0)))
% 0.46/0.66         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['25', '26'])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (![X7 : $i, X8 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.46/0.66           = (k3_xboole_0 @ X7 @ X8))),
% 0.46/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ sk_B_1)))
% 0.46/0.66         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.66      inference('split', [status(esa)], ['24'])).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B_1) = (k1_xboole_0)))
% 0.46/0.66         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['30', '31'])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.66      inference('split', [status(esa)], ['24'])).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B_1) = (sk_B_1)))
% 0.46/0.66         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.66      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (sk_B_1)))
% 0.46/0.66         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.66      inference('demod', [status(thm)], ['29', '34'])).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      ((((sk_A) != (k1_xboole_0))
% 0.46/0.66        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.46/0.66         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.46/0.66      inference('split', [status(esa)], ['36'])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          ((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ X0 @ X0)) != (k1_xboole_0)))
% 0.46/0.66         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.46/0.66             (((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['35', '37'])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.66      inference('split', [status(esa)], ['24'])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          ((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ X0 @ X0)) != (sk_B_1)))
% 0.46/0.66         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.46/0.66             (((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      ((((k1_xboole_0) != (sk_B_1)))
% 0.46/0.66         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.46/0.66             (((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['23', '40'])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.66      inference('split', [status(esa)], ['24'])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      ((((sk_B_1) != (sk_B_1)))
% 0.46/0.66         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.46/0.66             (((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.66      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.46/0.66       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['43'])).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.46/0.66       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.46/0.66      inference('split', [status(esa)], ['36'])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.46/0.66         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.46/0.66      inference('split', [status(esa)], ['24'])).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X17 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X17)
% 0.46/0.66          | ~ (r2_hidden @ X12 @ X17)
% 0.46/0.66          | ~ (r2_hidden @ X13 @ X15)
% 0.46/0.66          | ((X14) != (k4_tarski @ X12 @ X13)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      (![X12 : $i, X13 : $i, X15 : $i, X17 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X13 @ X15)
% 0.46/0.66          | ~ (r2_hidden @ X12 @ X17)
% 0.46/0.66          | (zip_tseitin_0 @ X13 @ X12 @ (k4_tarski @ X12 @ X13) @ X15 @ X17))),
% 0.46/0.66      inference('simplify', [status(thm)], ['49'])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.66         ((r1_xboole_0 @ X0 @ X1)
% 0.46/0.66          | (zip_tseitin_0 @ (sk_C @ X1 @ X0) @ X3 @ 
% 0.46/0.66             (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ X0 @ X2)
% 0.46/0.66          | ~ (r2_hidden @ X3 @ X2))),
% 0.46/0.66      inference('sup-', [status(thm)], ['48', '50'])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (((X0) = (k1_xboole_0))
% 0.46/0.66          | (zip_tseitin_0 @ (sk_C @ X2 @ X1) @ (sk_B @ X0) @ 
% 0.46/0.66             (k4_tarski @ (sk_B @ X0) @ (sk_C @ X2 @ X1)) @ X1 @ X0)
% 0.46/0.66          | (r1_xboole_0 @ X1 @ X2))),
% 0.46/0.66      inference('sup-', [status(thm)], ['47', '51'])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.66         (~ (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22)
% 0.46/0.66          | (r2_hidden @ X20 @ X23)
% 0.46/0.67          | ((X23) != (k2_zfmisc_1 @ X22 @ X21)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.67  thf('54', plain,
% 0.46/0.67      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.67         ((r2_hidden @ X20 @ (k2_zfmisc_1 @ X22 @ X21))
% 0.46/0.67          | ~ (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22))),
% 0.46/0.67      inference('simplify', [status(thm)], ['53'])).
% 0.46/0.67  thf('55', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ X1 @ X2)
% 0.46/0.67          | ((X0) = (k1_xboole_0))
% 0.46/0.67          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_C @ X2 @ X1)) @ 
% 0.46/0.67             (k2_zfmisc_1 @ X0 @ X1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['52', '54'])).
% 0.46/0.67  thf('56', plain,
% 0.46/0.67      ((![X0 : $i]:
% 0.46/0.67          ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ X0 @ sk_B_1)) @ 
% 0.46/0.67            k1_xboole_0)
% 0.46/0.67           | ((sk_A) = (k1_xboole_0))
% 0.46/0.67           | (r1_xboole_0 @ sk_B_1 @ X0)))
% 0.46/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.46/0.67      inference('sup+', [status(thm)], ['46', '55'])).
% 0.46/0.67  thf('57', plain,
% 0.46/0.67      ((![X0 : $i]:
% 0.46/0.67          ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ X0 @ sk_B_1)) @ 
% 0.46/0.67            k1_xboole_0)
% 0.46/0.67           | ((sk_A) = (k1_xboole_0))
% 0.46/0.67           | (r1_xboole_0 @ sk_B_1 @ X0)))
% 0.46/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.46/0.67      inference('sup+', [status(thm)], ['46', '55'])).
% 0.46/0.67  thf('58', plain,
% 0.46/0.67      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X2 @ X0)
% 0.46/0.67          | ~ (r2_hidden @ X2 @ X3)
% 0.46/0.67          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.67  thf('59', plain,
% 0.46/0.67      ((![X0 : $i, X1 : $i]:
% 0.46/0.67          ((r1_xboole_0 @ sk_B_1 @ X0)
% 0.46/0.67           | ((sk_A) = (k1_xboole_0))
% 0.46/0.67           | ~ (r1_xboole_0 @ k1_xboole_0 @ X1)
% 0.46/0.67           | ~ (r2_hidden @ 
% 0.46/0.67                (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ X0 @ sk_B_1)) @ X1)))
% 0.46/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['57', '58'])).
% 0.46/0.67  thf('60', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.46/0.67      inference('simplify', [status(thm)], ['9'])).
% 0.46/0.67  thf('61', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.67  thf('62', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.67  thf('63', plain,
% 0.46/0.67      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X2 @ X0)
% 0.46/0.67          | ~ (r2_hidden @ X2 @ X3)
% 0.46/0.67          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.67  thf('64', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ X0 @ X1)
% 0.46/0.67          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.46/0.67          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.46/0.67      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.67  thf('65', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ X0 @ X1)
% 0.46/0.67          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.46/0.67          | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['61', '64'])).
% 0.46/0.67  thf('66', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.67      inference('simplify', [status(thm)], ['65'])).
% 0.46/0.67  thf('67', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.46/0.67      inference('sup-', [status(thm)], ['60', '66'])).
% 0.46/0.67  thf('68', plain,
% 0.46/0.67      ((![X0 : $i, X1 : $i]:
% 0.46/0.67          ((r1_xboole_0 @ sk_B_1 @ X0)
% 0.46/0.67           | ((sk_A) = (k1_xboole_0))
% 0.46/0.67           | ~ (r2_hidden @ 
% 0.46/0.67                (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ X0 @ sk_B_1)) @ X1)))
% 0.46/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.46/0.67      inference('demod', [status(thm)], ['59', '67'])).
% 0.46/0.67  thf('69', plain,
% 0.46/0.67      ((![X0 : $i]:
% 0.46/0.67          ((r1_xboole_0 @ sk_B_1 @ X0)
% 0.46/0.67           | ((sk_A) = (k1_xboole_0))
% 0.46/0.67           | ((sk_A) = (k1_xboole_0))
% 0.46/0.67           | (r1_xboole_0 @ sk_B_1 @ X0)))
% 0.46/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['56', '68'])).
% 0.46/0.67  thf('70', plain,
% 0.46/0.67      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | (r1_xboole_0 @ sk_B_1 @ X0)))
% 0.46/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.46/0.67      inference('simplify', [status(thm)], ['69'])).
% 0.46/0.67  thf('71', plain,
% 0.46/0.67      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.46/0.67      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.67  thf('72', plain,
% 0.46/0.67      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.46/0.67      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.67  thf('73', plain,
% 0.46/0.67      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X2 @ X0)
% 0.46/0.67          | ~ (r2_hidden @ X2 @ X3)
% 0.46/0.67          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.67  thf('74', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (((X0) = (k1_xboole_0))
% 0.46/0.67          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.46/0.67          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['72', '73'])).
% 0.46/0.67  thf('75', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((X0) = (k1_xboole_0))
% 0.46/0.67          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.46/0.67          | ((X0) = (k1_xboole_0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['71', '74'])).
% 0.46/0.67  thf('76', plain,
% 0.46/0.67      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['75'])).
% 0.46/0.67  thf('77', plain,
% 0.46/0.67      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.46/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['70', '76'])).
% 0.46/0.67  thf('78', plain,
% 0.46/0.67      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.67      inference('split', [status(esa)], ['0'])).
% 0.46/0.67  thf('79', plain,
% 0.46/0.67      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.46/0.67       ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['43'])).
% 0.46/0.67  thf('80', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.46/0.67      inference('sat_resolution*', [status(thm)], ['1', '79'])).
% 0.46/0.67  thf('81', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.67      inference('simpl_trail', [status(thm)], ['78', '80'])).
% 0.46/0.67  thf('82', plain,
% 0.46/0.67      ((((sk_A) = (k1_xboole_0)))
% 0.46/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)], ['77', '81'])).
% 0.46/0.67  thf('83', plain,
% 0.46/0.67      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('split', [status(esa)], ['36'])).
% 0.46/0.67  thf('84', plain,
% 0.46/0.67      ((((sk_A) != (sk_A)))
% 0.46/0.67         <= (~ (((sk_A) = (k1_xboole_0))) & 
% 0.46/0.67             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['82', '83'])).
% 0.46/0.67  thf('85', plain,
% 0.46/0.67      ((((sk_A) = (k1_xboole_0))) | 
% 0.46/0.67       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['84'])).
% 0.46/0.67  thf('86', plain,
% 0.46/0.67      ((((sk_A) = (k1_xboole_0))) | 
% 0.46/0.67       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.46/0.67       (((sk_B_1) = (k1_xboole_0)))),
% 0.46/0.67      inference('split', [status(esa)], ['24'])).
% 0.46/0.67  thf('87', plain,
% 0.46/0.67      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('split', [status(esa)], ['24'])).
% 0.46/0.67  thf('88', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.67  thf('89', plain,
% 0.46/0.67      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_A) = (X0)))
% 0.46/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('sup+', [status(thm)], ['87', '88'])).
% 0.46/0.67  thf('90', plain,
% 0.46/0.67      (![X9 : $i, X11 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ X9 @ X11) | ((k4_xboole_0 @ X9 @ X11) != (X9)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.46/0.67  thf('91', plain,
% 0.46/0.67      ((![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ sk_A)))
% 0.46/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['89', '90'])).
% 0.46/0.67  thf('92', plain,
% 0.46/0.67      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('simplify', [status(thm)], ['91'])).
% 0.46/0.67  thf('93', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.46/0.67          | (zip_tseitin_0 @ 
% 0.46/0.67             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.46/0.67             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.46/0.67             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['12', '14'])).
% 0.46/0.67  thf('94', plain,
% 0.46/0.67      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.67         ((r2_hidden @ X12 @ X16)
% 0.46/0.67          | ~ (zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X16))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.67  thf('95', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 0.46/0.67          | (r2_hidden @ 
% 0.46/0.67             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['93', '94'])).
% 0.46/0.67  thf('96', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 0.46/0.67          | (r2_hidden @ 
% 0.46/0.67             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['93', '94'])).
% 0.46/0.67  thf('97', plain,
% 0.46/0.67      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X2 @ X0)
% 0.46/0.67          | ~ (r2_hidden @ X2 @ X3)
% 0.46/0.67          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.67  thf('98', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.67         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 0.46/0.67          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.46/0.67          | ~ (r2_hidden @ 
% 0.46/0.67               (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X2))),
% 0.46/0.67      inference('sup-', [status(thm)], ['96', '97'])).
% 0.46/0.67  thf('99', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 0.46/0.67          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.46/0.67          | ((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['95', '98'])).
% 0.46/0.67  thf('100', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (r1_xboole_0 @ X0 @ X0) | ((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['99'])).
% 0.46/0.67  thf('101', plain,
% 0.46/0.67      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (k1_xboole_0)))
% 0.46/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['92', '100'])).
% 0.46/0.67  thf('102', plain,
% 0.46/0.67      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('split', [status(esa)], ['24'])).
% 0.46/0.67  thf('103', plain,
% 0.46/0.67      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (sk_A)))
% 0.46/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('demod', [status(thm)], ['101', '102'])).
% 0.46/0.67  thf('104', plain,
% 0.46/0.67      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.46/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.46/0.67      inference('split', [status(esa)], ['36'])).
% 0.46/0.67  thf('105', plain,
% 0.46/0.67      ((((sk_A) != (k1_xboole_0)))
% 0.46/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.46/0.67             (((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['103', '104'])).
% 0.46/0.67  thf('106', plain,
% 0.46/0.67      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('split', [status(esa)], ['24'])).
% 0.46/0.67  thf('107', plain,
% 0.46/0.67      ((((sk_A) != (sk_A)))
% 0.46/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.46/0.67             (((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('demod', [status(thm)], ['105', '106'])).
% 0.46/0.67  thf('108', plain,
% 0.46/0.67      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.46/0.67       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['107'])).
% 0.46/0.67  thf('109', plain, ($false),
% 0.46/0.67      inference('sat_resolution*', [status(thm)],
% 0.46/0.67                ['1', '44', '45', '85', '86', '108'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7C78qlwaA5

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:01 EST 2020

% Result     : Theorem 3.41s
% Output     : Refutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 442 expanded)
%              Number of leaves         :   25 ( 131 expanded)
%              Depth                    :   22
%              Number of atoms          : 1182 (4023 expanded)
%              Number of equality atoms :  173 ( 611 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf('2',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X23: $i] :
      ( ( X23
        = ( k3_tarski @ X19 ) )
      | ( r2_hidden @ ( sk_D_1 @ X23 @ X19 ) @ X19 )
      | ( r2_hidden @ ( sk_C @ X23 @ X19 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( ( k4_xboole_0 @ X26 @ ( k1_tarski @ X25 ) )
       != X26 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('12',plain,
    ( k1_xboole_0
    = ( k3_tarski @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','13'])).

thf('15',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ X0 )
        | ( X0 = sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ ( k1_tarski @ X27 ) )
        = X26 )
      | ( r2_hidden @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

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

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X14 @ X11 @ X12 ) @ ( sk_E_1 @ X14 @ X11 @ X12 ) @ X14 @ X11 @ X12 )
      | ( X13
       != ( k2_zfmisc_1 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X14 @ X11 @ X12 ) @ ( sk_E_1 @ X14 @ X11 @ X12 ) @ X14 @ X11 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X2 @ X0 @ X1 ) @ ( sk_E_1 @ X2 @ X0 @ X1 ) @ X2 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ X5 )
      | ~ ( zip_tseitin_0 @ X3 @ X2 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k1_tarski @ X2 ) )
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F_1 @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( ( k4_xboole_0 @ X26 @ ( k1_tarski @ X25 ) )
       != X26 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
       != ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('35',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('38',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ( X15
        = ( k2_zfmisc_1 @ X12 @ X11 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X15 @ X11 @ X12 ) @ ( sk_E @ X15 @ X11 @ X12 ) @ ( sk_D @ X15 @ X11 @ X12 ) @ X11 @ X12 )
      | ( r2_hidden @ ( sk_D @ X15 @ X11 @ X12 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X2 @ X6 )
      | ~ ( zip_tseitin_0 @ X3 @ X2 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X2 @ X0 @ X1 ) @ ( sk_E_1 @ X2 @ X0 @ X1 ) @ X2 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('45',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X2 @ X6 )
      | ~ ( zip_tseitin_0 @ X3 @ X2 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k1_tarski @ X2 ) )
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E_1 @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( ( k4_xboole_0 @ X26 @ ( k1_tarski @ X25 ) )
       != X26 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['42','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['42','52'])).

thf('55',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('56',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ ( k1_tarski @ X27 ) )
        = X26 )
      | ( r2_hidden @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('57',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ ( k1_tarski @ X27 ) )
        = X26 )
      | ( r2_hidden @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('58',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X7: $i] :
      ( ( zip_tseitin_0 @ X3 @ X2 @ X4 @ X5 @ X7 )
      | ~ ( r2_hidden @ X2 @ X7 )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ( X4
       != ( k4_tarski @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('59',plain,(
    ! [X2: $i,X3: $i,X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X2 @ X7 )
      | ( zip_tseitin_0 @ X3 @ X2 @ ( k4_tarski @ X2 @ X3 ) @ X5 @ X7 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( zip_tseitin_0 @ X1 @ X3 @ ( k4_tarski @ X3 @ X1 ) @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( zip_tseitin_0 @ X3 @ X1 @ ( k4_tarski @ X1 @ X3 ) @ X2 @ X0 )
      | ( ( k4_xboole_0 @ X2 @ ( k1_tarski @ X3 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf('62',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X10 @ X13 )
      | ( X13
       != ( k2_zfmisc_1 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('63',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k2_zfmisc_1 @ X12 @ X11 ) )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X2 ) )
        = X1 )
      | ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X3 ) )
        = X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ k1_xboole_0 )
        | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ X1 ) )
          = sk_A )
        | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
          = sk_B ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('67',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
          = sk_B )
        | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ X1 ) )
          = sk_A ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( ( k4_xboole_0 @ X26 @ ( k1_tarski @ X25 ) )
       != X26 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('69',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_B != sk_B )
        | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ X1 ) )
          = sk_A )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ X1 ) )
          = sk_A ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ! [X1: $i] :
        ( ( sk_B = k1_xboole_0 )
        | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ X1 ) )
          = sk_A ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','70'])).

thf('72',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('74',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','73'])).

thf('75',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['72','74'])).

thf('76',plain,
    ( ! [X1: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ X1 ) )
        = sk_A )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['71','75'])).

thf('77',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( ( k4_xboole_0 @ X26 @ ( k1_tarski @ X25 ) )
       != X26 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ( sk_A != sk_A )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_A )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','79'])).

thf('81',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('82',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('85',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X0 )
        | ( X0
          = ( k3_tarski @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('89',plain,(
    ! [X19: $i,X23: $i] :
      ( ( X23
        = ( k3_tarski @ X19 ) )
      | ( r2_hidden @ ( sk_D_1 @ X23 @ X19 ) @ X19 )
      | ( r2_hidden @ ( sk_C @ X23 @ X19 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('90',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( ( k4_xboole_0 @ X26 @ ( k1_tarski @ X25 ) )
       != X26 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ( sk_A != sk_A )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_A @ X0 ) @ X0 )
        | ( sk_A
          = ( k3_tarski @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','97'])).

thf('99',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('100',plain,
    ( ( sk_A
      = ( k3_tarski @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X0 )
        | ( X0 = sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','88','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('107',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('109',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','83','84','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7C78qlwaA5
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.41/3.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.41/3.61  % Solved by: fo/fo7.sh
% 3.41/3.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.41/3.61  % done 1335 iterations in 3.162s
% 3.41/3.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.41/3.61  % SZS output start Refutation
% 3.41/3.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 3.41/3.61  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 3.41/3.61  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.41/3.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.41/3.61  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 3.41/3.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.41/3.61  thf(sk_B_type, type, sk_B: $i).
% 3.41/3.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.41/3.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.41/3.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.41/3.61  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 3.41/3.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.41/3.61  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 3.41/3.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.41/3.61  thf(sk_A_type, type, sk_A: $i).
% 3.41/3.61  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 3.41/3.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.41/3.61  thf(t113_zfmisc_1, conjecture,
% 3.41/3.61    (![A:$i,B:$i]:
% 3.41/3.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.41/3.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.41/3.61  thf(zf_stmt_0, negated_conjecture,
% 3.41/3.61    (~( ![A:$i,B:$i]:
% 3.41/3.61        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.41/3.61          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 3.41/3.61    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 3.41/3.61  thf('0', plain,
% 3.41/3.61      ((((sk_B) != (k1_xboole_0))
% 3.41/3.61        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 3.41/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.61  thf('1', plain,
% 3.41/3.61      (~ (((sk_B) = (k1_xboole_0))) | 
% 3.41/3.61       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 3.41/3.61      inference('split', [status(esa)], ['0'])).
% 3.41/3.61  thf('2', plain,
% 3.41/3.61      ((((sk_B) = (k1_xboole_0))
% 3.41/3.61        | ((sk_A) = (k1_xboole_0))
% 3.41/3.61        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 3.41/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.61  thf('3', plain, ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('split', [status(esa)], ['2'])).
% 3.41/3.61  thf(d4_tarski, axiom,
% 3.41/3.61    (![A:$i,B:$i]:
% 3.41/3.61     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 3.41/3.61       ( ![C:$i]:
% 3.41/3.61         ( ( r2_hidden @ C @ B ) <=>
% 3.41/3.61           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 3.41/3.61  thf('4', plain,
% 3.41/3.61      (![X19 : $i, X23 : $i]:
% 3.41/3.61         (((X23) = (k3_tarski @ X19))
% 3.41/3.61          | (r2_hidden @ (sk_D_1 @ X23 @ X19) @ X19)
% 3.41/3.61          | (r2_hidden @ (sk_C @ X23 @ X19) @ X23))),
% 3.41/3.61      inference('cnf', [status(esa)], [d4_tarski])).
% 3.41/3.61  thf(t4_boole, axiom,
% 3.41/3.61    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 3.41/3.61  thf('5', plain,
% 3.41/3.61      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.41/3.61      inference('cnf', [status(esa)], [t4_boole])).
% 3.41/3.61  thf(t65_zfmisc_1, axiom,
% 3.41/3.61    (![A:$i,B:$i]:
% 3.41/3.61     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 3.41/3.61       ( ~( r2_hidden @ B @ A ) ) ))).
% 3.41/3.61  thf('6', plain,
% 3.41/3.61      (![X25 : $i, X26 : $i]:
% 3.41/3.61         (~ (r2_hidden @ X25 @ X26)
% 3.41/3.61          | ((k4_xboole_0 @ X26 @ (k1_tarski @ X25)) != (X26)))),
% 3.41/3.61      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 3.41/3.61  thf('7', plain,
% 3.41/3.61      (![X0 : $i]:
% 3.41/3.61         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 3.41/3.61      inference('sup-', [status(thm)], ['5', '6'])).
% 3.41/3.61  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.41/3.61      inference('simplify', [status(thm)], ['7'])).
% 3.41/3.61  thf('9', plain,
% 3.41/3.61      (![X0 : $i]:
% 3.41/3.61         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 3.41/3.61          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 3.41/3.61      inference('sup-', [status(thm)], ['4', '8'])).
% 3.41/3.61  thf('10', plain,
% 3.41/3.61      (![X0 : $i]:
% 3.41/3.61         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 3.41/3.61          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 3.41/3.61      inference('sup-', [status(thm)], ['4', '8'])).
% 3.41/3.61  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.41/3.61      inference('simplify', [status(thm)], ['7'])).
% 3.41/3.61  thf('12', plain, (((k1_xboole_0) = (k3_tarski @ k1_xboole_0))),
% 3.41/3.61      inference('sup-', [status(thm)], ['10', '11'])).
% 3.41/3.61  thf('13', plain,
% 3.41/3.61      (![X0 : $i]:
% 3.41/3.61         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 3.41/3.61      inference('demod', [status(thm)], ['9', '12'])).
% 3.41/3.61  thf('14', plain,
% 3.41/3.61      ((![X0 : $i]:
% 3.41/3.61          ((r2_hidden @ (sk_C @ X0 @ sk_B) @ X0) | ((X0) = (k1_xboole_0))))
% 3.41/3.61         <= ((((sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('sup+', [status(thm)], ['3', '13'])).
% 3.41/3.61  thf('15', plain,
% 3.41/3.61      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('split', [status(esa)], ['2'])).
% 3.41/3.61  thf('16', plain,
% 3.41/3.61      ((![X0 : $i]: ((r2_hidden @ (sk_C @ X0 @ sk_B) @ X0) | ((X0) = (sk_B))))
% 3.41/3.61         <= ((((sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('demod', [status(thm)], ['14', '15'])).
% 3.41/3.61  thf('17', plain,
% 3.41/3.61      (![X26 : $i, X27 : $i]:
% 3.41/3.61         (((k4_xboole_0 @ X26 @ (k1_tarski @ X27)) = (X26))
% 3.41/3.61          | (r2_hidden @ X27 @ X26))),
% 3.41/3.61      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 3.41/3.61  thf(d2_zfmisc_1, axiom,
% 3.41/3.61    (![A:$i,B:$i,C:$i]:
% 3.41/3.61     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 3.41/3.61       ( ![D:$i]:
% 3.41/3.61         ( ( r2_hidden @ D @ C ) <=>
% 3.41/3.61           ( ?[E:$i,F:$i]:
% 3.41/3.61             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 3.41/3.61               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 3.41/3.61  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 3.41/3.61  thf(zf_stmt_2, axiom,
% 3.41/3.61    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 3.41/3.61     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 3.41/3.61       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 3.41/3.61         ( r2_hidden @ E @ A ) ) ))).
% 3.41/3.61  thf(zf_stmt_3, axiom,
% 3.41/3.61    (![A:$i,B:$i,C:$i]:
% 3.41/3.61     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 3.41/3.61       ( ![D:$i]:
% 3.41/3.61         ( ( r2_hidden @ D @ C ) <=>
% 3.41/3.61           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 3.41/3.61  thf('18', plain,
% 3.41/3.61      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 3.41/3.61         (~ (r2_hidden @ X14 @ X13)
% 3.41/3.61          | (zip_tseitin_0 @ (sk_F_1 @ X14 @ X11 @ X12) @ 
% 3.41/3.61             (sk_E_1 @ X14 @ X11 @ X12) @ X14 @ X11 @ X12)
% 3.41/3.61          | ((X13) != (k2_zfmisc_1 @ X12 @ X11)))),
% 3.41/3.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.41/3.61  thf('19', plain,
% 3.41/3.61      (![X11 : $i, X12 : $i, X14 : $i]:
% 3.41/3.61         ((zip_tseitin_0 @ (sk_F_1 @ X14 @ X11 @ X12) @ 
% 3.41/3.61           (sk_E_1 @ X14 @ X11 @ X12) @ X14 @ X11 @ X12)
% 3.41/3.61          | ~ (r2_hidden @ X14 @ (k2_zfmisc_1 @ X12 @ X11)))),
% 3.41/3.61      inference('simplify', [status(thm)], ['18'])).
% 3.41/3.61  thf('20', plain,
% 3.41/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.41/3.61         (((k4_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k1_tarski @ X2))
% 3.41/3.61            = (k2_zfmisc_1 @ X1 @ X0))
% 3.41/3.61          | (zip_tseitin_0 @ (sk_F_1 @ X2 @ X0 @ X1) @ 
% 3.41/3.61             (sk_E_1 @ X2 @ X0 @ X1) @ X2 @ X0 @ X1))),
% 3.41/3.61      inference('sup-', [status(thm)], ['17', '19'])).
% 3.41/3.61  thf('21', plain,
% 3.41/3.61      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 3.41/3.61         ((r2_hidden @ X3 @ X5) | ~ (zip_tseitin_0 @ X3 @ X2 @ X4 @ X5 @ X6))),
% 3.41/3.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.41/3.61  thf('22', plain,
% 3.41/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.41/3.61         (((k4_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k1_tarski @ X2))
% 3.41/3.61            = (k2_zfmisc_1 @ X0 @ X1))
% 3.41/3.61          | (r2_hidden @ (sk_F_1 @ X2 @ X1 @ X0) @ X1))),
% 3.41/3.61      inference('sup-', [status(thm)], ['20', '21'])).
% 3.41/3.61  thf('23', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.41/3.61      inference('simplify', [status(thm)], ['7'])).
% 3.41/3.61  thf('24', plain,
% 3.41/3.61      (![X0 : $i, X1 : $i]:
% 3.41/3.61         ((k4_xboole_0 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0) @ (k1_tarski @ X1))
% 3.41/3.61           = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 3.41/3.61      inference('sup-', [status(thm)], ['22', '23'])).
% 3.41/3.61  thf('25', plain,
% 3.41/3.61      (![X25 : $i, X26 : $i]:
% 3.41/3.61         (~ (r2_hidden @ X25 @ X26)
% 3.41/3.61          | ((k4_xboole_0 @ X26 @ (k1_tarski @ X25)) != (X26)))),
% 3.41/3.61      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 3.41/3.61  thf('26', plain,
% 3.41/3.61      (![X0 : $i, X1 : $i]:
% 3.41/3.61         (((k2_zfmisc_1 @ X0 @ k1_xboole_0) != (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 3.41/3.61          | ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)))),
% 3.41/3.61      inference('sup-', [status(thm)], ['24', '25'])).
% 3.41/3.61  thf('27', plain,
% 3.41/3.61      (![X0 : $i, X1 : $i]:
% 3.41/3.61         ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 3.41/3.61      inference('simplify', [status(thm)], ['26'])).
% 3.41/3.61  thf('28', plain,
% 3.41/3.61      ((![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (sk_B)))
% 3.41/3.61         <= ((((sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('sup-', [status(thm)], ['16', '27'])).
% 3.41/3.61  thf('29', plain,
% 3.41/3.61      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('split', [status(esa)], ['2'])).
% 3.41/3.61  thf('30', plain,
% 3.41/3.61      ((![X0 : $i]: ((k2_zfmisc_1 @ X0 @ sk_B) = (sk_B)))
% 3.41/3.61         <= ((((sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('demod', [status(thm)], ['28', '29'])).
% 3.41/3.61  thf('31', plain,
% 3.41/3.61      ((((sk_A) != (k1_xboole_0))
% 3.41/3.61        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 3.41/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.61  thf('32', plain,
% 3.41/3.61      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 3.41/3.61         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('split', [status(esa)], ['31'])).
% 3.41/3.61  thf('33', plain,
% 3.41/3.61      ((((sk_B) != (k1_xboole_0)))
% 3.41/3.61         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 3.41/3.61             (((sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('sup-', [status(thm)], ['30', '32'])).
% 3.41/3.61  thf('34', plain,
% 3.41/3.61      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('split', [status(esa)], ['2'])).
% 3.41/3.61  thf('35', plain,
% 3.41/3.61      ((((sk_B) != (sk_B)))
% 3.41/3.61         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 3.41/3.61             (((sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('demod', [status(thm)], ['33', '34'])).
% 3.41/3.61  thf('36', plain,
% 3.41/3.61      (~ (((sk_B) = (k1_xboole_0))) | 
% 3.41/3.61       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 3.41/3.61      inference('simplify', [status(thm)], ['35'])).
% 3.41/3.61  thf('37', plain,
% 3.41/3.61      (~ (((sk_A) = (k1_xboole_0))) | 
% 3.41/3.61       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 3.41/3.61      inference('split', [status(esa)], ['31'])).
% 3.41/3.61  thf('38', plain,
% 3.41/3.61      (![X11 : $i, X12 : $i, X15 : $i]:
% 3.41/3.61         (((X15) = (k2_zfmisc_1 @ X12 @ X11))
% 3.41/3.61          | (zip_tseitin_0 @ (sk_F @ X15 @ X11 @ X12) @ 
% 3.41/3.61             (sk_E @ X15 @ X11 @ X12) @ (sk_D @ X15 @ X11 @ X12) @ X11 @ X12)
% 3.41/3.61          | (r2_hidden @ (sk_D @ X15 @ X11 @ X12) @ X15))),
% 3.41/3.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.41/3.61  thf('39', plain,
% 3.41/3.61      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 3.41/3.61         ((r2_hidden @ X2 @ X6) | ~ (zip_tseitin_0 @ X3 @ X2 @ X4 @ X5 @ X6))),
% 3.41/3.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.41/3.61  thf('40', plain,
% 3.41/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.41/3.61         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 3.41/3.61          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 3.41/3.61          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 3.41/3.61      inference('sup-', [status(thm)], ['38', '39'])).
% 3.41/3.61  thf('41', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.41/3.61      inference('simplify', [status(thm)], ['7'])).
% 3.41/3.61  thf('42', plain,
% 3.41/3.61      (![X0 : $i, X1 : $i]:
% 3.41/3.61         (((X1) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 3.41/3.61          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1))),
% 3.41/3.61      inference('sup-', [status(thm)], ['40', '41'])).
% 3.41/3.61  thf('43', plain,
% 3.41/3.61      (![X0 : $i]:
% 3.41/3.61         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 3.41/3.61      inference('demod', [status(thm)], ['9', '12'])).
% 3.41/3.61  thf('44', plain,
% 3.41/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.41/3.61         (((k4_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k1_tarski @ X2))
% 3.41/3.61            = (k2_zfmisc_1 @ X1 @ X0))
% 3.41/3.61          | (zip_tseitin_0 @ (sk_F_1 @ X2 @ X0 @ X1) @ 
% 3.41/3.61             (sk_E_1 @ X2 @ X0 @ X1) @ X2 @ X0 @ X1))),
% 3.41/3.61      inference('sup-', [status(thm)], ['17', '19'])).
% 3.41/3.61  thf('45', plain,
% 3.41/3.61      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 3.41/3.61         ((r2_hidden @ X2 @ X6) | ~ (zip_tseitin_0 @ X3 @ X2 @ X4 @ X5 @ X6))),
% 3.41/3.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.41/3.61  thf('46', plain,
% 3.41/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.41/3.61         (((k4_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k1_tarski @ X2))
% 3.41/3.61            = (k2_zfmisc_1 @ X0 @ X1))
% 3.41/3.61          | (r2_hidden @ (sk_E_1 @ X2 @ X1 @ X0) @ X0))),
% 3.41/3.61      inference('sup-', [status(thm)], ['44', '45'])).
% 3.41/3.61  thf('47', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.41/3.61      inference('simplify', [status(thm)], ['7'])).
% 3.41/3.61  thf('48', plain,
% 3.41/3.61      (![X0 : $i, X1 : $i]:
% 3.41/3.61         ((k4_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ (k1_tarski @ X1))
% 3.41/3.61           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 3.41/3.61      inference('sup-', [status(thm)], ['46', '47'])).
% 3.41/3.61  thf('49', plain,
% 3.41/3.61      (![X25 : $i, X26 : $i]:
% 3.41/3.61         (~ (r2_hidden @ X25 @ X26)
% 3.41/3.61          | ((k4_xboole_0 @ X26 @ (k1_tarski @ X25)) != (X26)))),
% 3.41/3.61      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 3.41/3.61  thf('50', plain,
% 3.41/3.61      (![X0 : $i, X1 : $i]:
% 3.41/3.61         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 3.41/3.61          | ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 3.41/3.61      inference('sup-', [status(thm)], ['48', '49'])).
% 3.41/3.61  thf('51', plain,
% 3.41/3.61      (![X0 : $i, X1 : $i]:
% 3.41/3.61         ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 3.41/3.61      inference('simplify', [status(thm)], ['50'])).
% 3.41/3.61  thf('52', plain,
% 3.41/3.61      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.41/3.61      inference('sup-', [status(thm)], ['43', '51'])).
% 3.41/3.61  thf('53', plain,
% 3.41/3.61      (![X0 : $i, X1 : $i]:
% 3.41/3.61         (((X1) = (k1_xboole_0))
% 3.41/3.61          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1))),
% 3.41/3.61      inference('demod', [status(thm)], ['42', '52'])).
% 3.41/3.61  thf('54', plain,
% 3.41/3.61      (![X0 : $i, X1 : $i]:
% 3.41/3.61         (((X1) = (k1_xboole_0))
% 3.41/3.61          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1))),
% 3.41/3.61      inference('demod', [status(thm)], ['42', '52'])).
% 3.41/3.61  thf('55', plain,
% 3.41/3.61      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 3.41/3.61         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('split', [status(esa)], ['2'])).
% 3.41/3.61  thf('56', plain,
% 3.41/3.61      (![X26 : $i, X27 : $i]:
% 3.41/3.61         (((k4_xboole_0 @ X26 @ (k1_tarski @ X27)) = (X26))
% 3.41/3.61          | (r2_hidden @ X27 @ X26))),
% 3.41/3.61      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 3.41/3.61  thf('57', plain,
% 3.41/3.61      (![X26 : $i, X27 : $i]:
% 3.41/3.61         (((k4_xboole_0 @ X26 @ (k1_tarski @ X27)) = (X26))
% 3.41/3.61          | (r2_hidden @ X27 @ X26))),
% 3.41/3.61      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 3.41/3.61  thf('58', plain,
% 3.41/3.61      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X7 : $i]:
% 3.41/3.61         ((zip_tseitin_0 @ X3 @ X2 @ X4 @ X5 @ X7)
% 3.41/3.61          | ~ (r2_hidden @ X2 @ X7)
% 3.41/3.61          | ~ (r2_hidden @ X3 @ X5)
% 3.41/3.61          | ((X4) != (k4_tarski @ X2 @ X3)))),
% 3.41/3.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.41/3.61  thf('59', plain,
% 3.41/3.61      (![X2 : $i, X3 : $i, X5 : $i, X7 : $i]:
% 3.41/3.61         (~ (r2_hidden @ X3 @ X5)
% 3.41/3.61          | ~ (r2_hidden @ X2 @ X7)
% 3.41/3.61          | (zip_tseitin_0 @ X3 @ X2 @ (k4_tarski @ X2 @ X3) @ X5 @ X7))),
% 3.41/3.61      inference('simplify', [status(thm)], ['58'])).
% 3.41/3.61  thf('60', plain,
% 3.41/3.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.41/3.61         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 3.41/3.61          | (zip_tseitin_0 @ X1 @ X3 @ (k4_tarski @ X3 @ X1) @ X0 @ X2)
% 3.41/3.61          | ~ (r2_hidden @ X3 @ X2))),
% 3.41/3.61      inference('sup-', [status(thm)], ['57', '59'])).
% 3.41/3.61  thf('61', plain,
% 3.41/3.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.41/3.61         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 3.41/3.61          | (zip_tseitin_0 @ X3 @ X1 @ (k4_tarski @ X1 @ X3) @ X2 @ X0)
% 3.41/3.61          | ((k4_xboole_0 @ X2 @ (k1_tarski @ X3)) = (X2)))),
% 3.41/3.61      inference('sup-', [status(thm)], ['56', '60'])).
% 3.41/3.61  thf('62', plain,
% 3.41/3.61      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.41/3.61         (~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 @ X12)
% 3.41/3.61          | (r2_hidden @ X10 @ X13)
% 3.41/3.61          | ((X13) != (k2_zfmisc_1 @ X12 @ X11)))),
% 3.41/3.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.41/3.61  thf('63', plain,
% 3.41/3.61      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 3.41/3.61         ((r2_hidden @ X10 @ (k2_zfmisc_1 @ X12 @ X11))
% 3.41/3.61          | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 @ X12))),
% 3.41/3.61      inference('simplify', [status(thm)], ['62'])).
% 3.41/3.61  thf('64', plain,
% 3.41/3.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.41/3.61         (((k4_xboole_0 @ X1 @ (k1_tarski @ X2)) = (X1))
% 3.41/3.61          | ((k4_xboole_0 @ X0 @ (k1_tarski @ X3)) = (X0))
% 3.41/3.61          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 3.41/3.61      inference('sup-', [status(thm)], ['61', '63'])).
% 3.41/3.61  thf('65', plain,
% 3.41/3.61      ((![X0 : $i, X1 : $i]:
% 3.41/3.61          ((r2_hidden @ (k4_tarski @ X1 @ X0) @ k1_xboole_0)
% 3.41/3.61           | ((k4_xboole_0 @ sk_A @ (k1_tarski @ X1)) = (sk_A))
% 3.41/3.61           | ((k4_xboole_0 @ sk_B @ (k1_tarski @ X0)) = (sk_B))))
% 3.41/3.61         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('sup+', [status(thm)], ['55', '64'])).
% 3.41/3.61  thf('66', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.41/3.61      inference('simplify', [status(thm)], ['7'])).
% 3.41/3.61  thf('67', plain,
% 3.41/3.61      ((![X0 : $i, X1 : $i]:
% 3.41/3.61          (((k4_xboole_0 @ sk_B @ (k1_tarski @ X0)) = (sk_B))
% 3.41/3.61           | ((k4_xboole_0 @ sk_A @ (k1_tarski @ X1)) = (sk_A))))
% 3.41/3.61         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('clc', [status(thm)], ['65', '66'])).
% 3.41/3.61  thf('68', plain,
% 3.41/3.61      (![X25 : $i, X26 : $i]:
% 3.41/3.61         (~ (r2_hidden @ X25 @ X26)
% 3.41/3.61          | ((k4_xboole_0 @ X26 @ (k1_tarski @ X25)) != (X26)))),
% 3.41/3.61      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 3.41/3.61  thf('69', plain,
% 3.41/3.61      ((![X0 : $i, X1 : $i]:
% 3.41/3.61          (((sk_B) != (sk_B))
% 3.41/3.61           | ((k4_xboole_0 @ sk_A @ (k1_tarski @ X1)) = (sk_A))
% 3.41/3.61           | ~ (r2_hidden @ X0 @ sk_B)))
% 3.41/3.61         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('sup-', [status(thm)], ['67', '68'])).
% 3.41/3.61  thf('70', plain,
% 3.41/3.61      ((![X0 : $i, X1 : $i]:
% 3.41/3.61          (~ (r2_hidden @ X0 @ sk_B)
% 3.41/3.61           | ((k4_xboole_0 @ sk_A @ (k1_tarski @ X1)) = (sk_A))))
% 3.41/3.61         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('simplify', [status(thm)], ['69'])).
% 3.41/3.61  thf('71', plain,
% 3.41/3.61      ((![X1 : $i]:
% 3.41/3.61          (((sk_B) = (k1_xboole_0))
% 3.41/3.61           | ((k4_xboole_0 @ sk_A @ (k1_tarski @ X1)) = (sk_A))))
% 3.41/3.61         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('sup-', [status(thm)], ['54', '70'])).
% 3.41/3.61  thf('72', plain,
% 3.41/3.61      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('split', [status(esa)], ['0'])).
% 3.41/3.61  thf('73', plain,
% 3.41/3.61      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 3.41/3.61       ~ (((sk_B) = (k1_xboole_0)))),
% 3.41/3.61      inference('simplify', [status(thm)], ['35'])).
% 3.41/3.61  thf('74', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 3.41/3.61      inference('sat_resolution*', [status(thm)], ['1', '73'])).
% 3.41/3.61  thf('75', plain, (((sk_B) != (k1_xboole_0))),
% 3.41/3.61      inference('simpl_trail', [status(thm)], ['72', '74'])).
% 3.41/3.61  thf('76', plain,
% 3.41/3.61      ((![X1 : $i]: ((k4_xboole_0 @ sk_A @ (k1_tarski @ X1)) = (sk_A)))
% 3.41/3.61         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('simplify_reflect-', [status(thm)], ['71', '75'])).
% 3.41/3.61  thf('77', plain,
% 3.41/3.61      (![X25 : $i, X26 : $i]:
% 3.41/3.61         (~ (r2_hidden @ X25 @ X26)
% 3.41/3.61          | ((k4_xboole_0 @ X26 @ (k1_tarski @ X25)) != (X26)))),
% 3.41/3.61      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 3.41/3.61  thf('78', plain,
% 3.41/3.61      ((![X0 : $i]: (((sk_A) != (sk_A)) | ~ (r2_hidden @ X0 @ sk_A)))
% 3.41/3.61         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('sup-', [status(thm)], ['76', '77'])).
% 3.41/3.61  thf('79', plain,
% 3.41/3.61      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A))
% 3.41/3.61         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('simplify', [status(thm)], ['78'])).
% 3.41/3.61  thf('80', plain,
% 3.41/3.61      ((((sk_A) = (k1_xboole_0)))
% 3.41/3.61         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('sup-', [status(thm)], ['53', '79'])).
% 3.41/3.61  thf('81', plain,
% 3.41/3.61      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('split', [status(esa)], ['31'])).
% 3.41/3.61  thf('82', plain,
% 3.41/3.61      ((((sk_A) != (sk_A)))
% 3.41/3.61         <= (~ (((sk_A) = (k1_xboole_0))) & 
% 3.41/3.61             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('sup-', [status(thm)], ['80', '81'])).
% 3.41/3.61  thf('83', plain,
% 3.41/3.61      ((((sk_A) = (k1_xboole_0))) | 
% 3.41/3.61       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 3.41/3.61      inference('simplify', [status(thm)], ['82'])).
% 3.41/3.61  thf('84', plain,
% 3.41/3.61      ((((sk_A) = (k1_xboole_0))) | 
% 3.41/3.61       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 3.41/3.61       (((sk_B) = (k1_xboole_0)))),
% 3.41/3.61      inference('split', [status(esa)], ['2'])).
% 3.41/3.61  thf('85', plain,
% 3.41/3.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('split', [status(esa)], ['2'])).
% 3.41/3.61  thf('86', plain,
% 3.41/3.61      (![X0 : $i]:
% 3.41/3.61         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 3.41/3.61          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 3.41/3.61      inference('sup-', [status(thm)], ['4', '8'])).
% 3.41/3.61  thf('87', plain,
% 3.41/3.61      ((![X0 : $i]:
% 3.41/3.61          ((r2_hidden @ (sk_C @ X0 @ sk_A) @ X0)
% 3.41/3.61           | ((X0) = (k3_tarski @ k1_xboole_0))))
% 3.41/3.61         <= ((((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('sup+', [status(thm)], ['85', '86'])).
% 3.41/3.61  thf('88', plain,
% 3.41/3.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('split', [status(esa)], ['2'])).
% 3.41/3.61  thf('89', plain,
% 3.41/3.61      (![X19 : $i, X23 : $i]:
% 3.41/3.61         (((X23) = (k3_tarski @ X19))
% 3.41/3.61          | (r2_hidden @ (sk_D_1 @ X23 @ X19) @ X19)
% 3.41/3.61          | (r2_hidden @ (sk_C @ X23 @ X19) @ X23))),
% 3.41/3.61      inference('cnf', [status(esa)], [d4_tarski])).
% 3.41/3.61  thf('90', plain,
% 3.41/3.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('split', [status(esa)], ['2'])).
% 3.41/3.61  thf('91', plain,
% 3.41/3.61      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.41/3.61      inference('cnf', [status(esa)], [t4_boole])).
% 3.41/3.61  thf('92', plain,
% 3.41/3.61      ((![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0)))
% 3.41/3.61         <= ((((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('sup+', [status(thm)], ['90', '91'])).
% 3.41/3.61  thf('93', plain,
% 3.41/3.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('split', [status(esa)], ['2'])).
% 3.41/3.61  thf('94', plain,
% 3.41/3.61      ((![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (sk_A)))
% 3.41/3.61         <= ((((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('demod', [status(thm)], ['92', '93'])).
% 3.41/3.61  thf('95', plain,
% 3.41/3.61      (![X25 : $i, X26 : $i]:
% 3.41/3.61         (~ (r2_hidden @ X25 @ X26)
% 3.41/3.61          | ((k4_xboole_0 @ X26 @ (k1_tarski @ X25)) != (X26)))),
% 3.41/3.61      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 3.41/3.61  thf('96', plain,
% 3.41/3.61      ((![X0 : $i]: (((sk_A) != (sk_A)) | ~ (r2_hidden @ X0 @ sk_A)))
% 3.41/3.61         <= ((((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('sup-', [status(thm)], ['94', '95'])).
% 3.41/3.61  thf('97', plain,
% 3.41/3.61      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('simplify', [status(thm)], ['96'])).
% 3.41/3.61  thf('98', plain,
% 3.41/3.61      ((![X0 : $i]:
% 3.41/3.61          ((r2_hidden @ (sk_D_1 @ sk_A @ X0) @ X0)
% 3.41/3.61           | ((sk_A) = (k3_tarski @ X0))))
% 3.41/3.61         <= ((((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('sup-', [status(thm)], ['89', '97'])).
% 3.41/3.61  thf('99', plain,
% 3.41/3.61      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('simplify', [status(thm)], ['96'])).
% 3.41/3.61  thf('100', plain,
% 3.41/3.61      ((((sk_A) = (k3_tarski @ sk_A))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('sup-', [status(thm)], ['98', '99'])).
% 3.41/3.61  thf('101', plain,
% 3.41/3.61      ((![X0 : $i]: ((r2_hidden @ (sk_C @ X0 @ sk_A) @ X0) | ((X0) = (sk_A))))
% 3.41/3.61         <= ((((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('demod', [status(thm)], ['87', '88', '100'])).
% 3.41/3.61  thf('102', plain,
% 3.41/3.61      (![X0 : $i, X1 : $i]:
% 3.41/3.61         ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 3.41/3.61      inference('simplify', [status(thm)], ['50'])).
% 3.41/3.61  thf('103', plain,
% 3.41/3.61      ((![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (sk_A)))
% 3.41/3.61         <= ((((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('sup-', [status(thm)], ['101', '102'])).
% 3.41/3.61  thf('104', plain,
% 3.41/3.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('split', [status(esa)], ['2'])).
% 3.41/3.61  thf('105', plain,
% 3.41/3.61      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (sk_A)))
% 3.41/3.61         <= ((((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('demod', [status(thm)], ['103', '104'])).
% 3.41/3.61  thf('106', plain,
% 3.41/3.61      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 3.41/3.61         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.41/3.61      inference('split', [status(esa)], ['31'])).
% 3.41/3.61  thf('107', plain,
% 3.41/3.61      ((((sk_A) != (k1_xboole_0)))
% 3.41/3.61         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 3.41/3.61             (((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('sup-', [status(thm)], ['105', '106'])).
% 3.41/3.61  thf('108', plain,
% 3.41/3.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('split', [status(esa)], ['2'])).
% 3.41/3.61  thf('109', plain,
% 3.41/3.61      ((((sk_A) != (sk_A)))
% 3.41/3.61         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 3.41/3.61             (((sk_A) = (k1_xboole_0))))),
% 3.41/3.61      inference('demod', [status(thm)], ['107', '108'])).
% 3.41/3.61  thf('110', plain,
% 3.41/3.61      (~ (((sk_A) = (k1_xboole_0))) | 
% 3.41/3.61       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 3.41/3.61      inference('simplify', [status(thm)], ['109'])).
% 3.41/3.61  thf('111', plain, ($false),
% 3.41/3.61      inference('sat_resolution*', [status(thm)],
% 3.41/3.61                ['1', '36', '37', '83', '84', '110'])).
% 3.41/3.61  
% 3.41/3.61  % SZS output end Refutation
% 3.41/3.61  
% 3.41/3.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

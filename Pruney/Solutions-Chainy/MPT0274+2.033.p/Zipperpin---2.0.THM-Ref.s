%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BE4rVsoSYk

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:36 EST 2020

% Result     : Theorem 37.27s
% Output     : Refutation 37.27s
% Verified   : 
% Statistics : Number of formulae       :  131 (1270 expanded)
%              Number of leaves         :   16 ( 313 expanded)
%              Depth                    :   26
%              Number of atoms          : 1408 (17343 expanded)
%              Number of equality atoms :   97 (1223 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t72_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
      <=> ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t72_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( r2_hidden @ X11 @ X15 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ~ ( zip_tseitin_0 @ X6 @ X8 @ X9 @ X6 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('34',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ X1 )
        | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ X0 ) @ X1 ) ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('42',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','52'])).

thf('54',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ X1 )
        | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ sk_C @ X1 ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['34','53'])).

thf('55',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ sk_C @ X0 ) ) )
        | ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(condensation,[status(thm)],['54'])).

thf('56',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X1 @ sk_C ) )
        | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X0 @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['27','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('58',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['59'])).

thf('61',plain,
    ( ! [X1: $i] :
        ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['56','60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
        = ( k2_tarski @ sk_A @ sk_B ) )
      & ( r2_hidden @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','61'])).

thf('63',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('65',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X8 )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('66',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X8 @ X9 @ X6 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('70',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ X0 )
        | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_C @ X0 ) ) )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('74',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ sk_B @ X0 )
        | ( r2_hidden @ sk_B @ X1 )
        | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ X0 ) @ X1 ) ) )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','52'])).

thf('76',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( r2_hidden @ sk_B @ X0 )
        | ( r2_hidden @ sk_B @ X1 )
        | ~ ( r2_hidden @ sk_B @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ sk_C @ X1 ) ) ) )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ sk_B @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ sk_C @ X0 ) ) )
        | ( r2_hidden @ sk_B @ X0 ) )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(condensation,[status(thm)],['76'])).

thf('78',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ sk_B @ ( k4_xboole_0 @ X1 @ sk_C ) )
        | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ X0 @ X0 ) ) )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['69','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['59'])).

thf('80',plain,
    ( ! [X1: $i] :
        ~ ( r2_hidden @ sk_B @ ( k4_xboole_0 @ X1 @ sk_C ) )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
        = ( k2_tarski @ sk_A @ sk_B ) )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['68','80'])).

thf('82',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','81'])).

thf('83',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('84',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('85',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['3','63','82','83','84'])).

thf('86',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','85'])).

thf('87',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( X7 = X8 )
      | ( X7 = X9 )
      | ( X7 = X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('89',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('90',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('91',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X2 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ X2 @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X0 )
      | ( ( sk_D @ X2 @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X0 )
      | ( ( sk_D @ X2 @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X1 )
      | ( X2
        = ( k4_xboole_0 @ X2 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['87','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( ( sk_D @ X2 @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X1 )
      | ( ( sk_D @ X2 @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( sk_D @ X1 @ ( k2_tarski @ X2 @ X0 ) @ X1 )
        = X2 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) )
      | ( ( sk_D @ X1 @ ( k2_tarski @ X2 @ X0 ) @ X1 )
        = X2 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X2 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X2 ) ) )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X2 ) ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X2 ) ) )
      | ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X2 @ X1 )
        = ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['28'])).

thf('105',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','63','82','83'])).

thf('106',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('110',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['3','63'])).

thf('111',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['109','110'])).

thf('112',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['108','111'])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['86','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BE4rVsoSYk
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:36:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 37.27/37.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 37.27/37.51  % Solved by: fo/fo7.sh
% 37.27/37.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 37.27/37.51  % done 17585 iterations in 37.036s
% 37.27/37.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 37.27/37.51  % SZS output start Refutation
% 37.27/37.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 37.27/37.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 37.27/37.51  thf(sk_A_type, type, sk_A: $i).
% 37.27/37.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 37.27/37.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 37.27/37.51  thf(sk_C_type, type, sk_C: $i).
% 37.27/37.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 37.27/37.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 37.27/37.51  thf(sk_B_type, type, sk_B: $i).
% 37.27/37.51  thf(t72_zfmisc_1, conjecture,
% 37.27/37.51    (![A:$i,B:$i,C:$i]:
% 37.27/37.51     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 37.27/37.51       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 37.27/37.51  thf(zf_stmt_0, negated_conjecture,
% 37.27/37.51    (~( ![A:$i,B:$i,C:$i]:
% 37.27/37.51        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 37.27/37.51          ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ) )),
% 37.27/37.51    inference('cnf.neg', [status(esa)], [t72_zfmisc_1])).
% 37.27/37.51  thf('0', plain,
% 37.27/37.51      ((~ (r2_hidden @ sk_B @ sk_C)
% 37.27/37.51        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 37.27/37.51            = (k2_tarski @ sk_A @ sk_B)))),
% 37.27/37.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.27/37.51  thf('1', plain,
% 37.27/37.51      ((~ (r2_hidden @ sk_B @ sk_C)) <= (~ ((r2_hidden @ sk_B @ sk_C)))),
% 37.27/37.51      inference('split', [status(esa)], ['0'])).
% 37.27/37.51  thf('2', plain,
% 37.27/37.51      ((~ (r2_hidden @ sk_A @ sk_C)
% 37.27/37.51        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 37.27/37.51            = (k2_tarski @ sk_A @ sk_B)))),
% 37.27/37.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.27/37.51  thf('3', plain,
% 37.27/37.51      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 37.27/37.51       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 37.27/37.51          = (k2_tarski @ sk_A @ sk_B)))),
% 37.27/37.51      inference('split', [status(esa)], ['2'])).
% 37.27/37.51  thf(t70_enumset1, axiom,
% 37.27/37.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 37.27/37.51  thf('4', plain,
% 37.27/37.51      (![X18 : $i, X19 : $i]:
% 37.27/37.51         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 37.27/37.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 37.27/37.51  thf(d1_enumset1, axiom,
% 37.27/37.51    (![A:$i,B:$i,C:$i,D:$i]:
% 37.27/37.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 37.27/37.51       ( ![E:$i]:
% 37.27/37.51         ( ( r2_hidden @ E @ D ) <=>
% 37.27/37.51           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 37.27/37.51  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 37.27/37.51  thf(zf_stmt_2, axiom,
% 37.27/37.51    (![E:$i,C:$i,B:$i,A:$i]:
% 37.27/37.51     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 37.27/37.51       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 37.27/37.51  thf(zf_stmt_3, axiom,
% 37.27/37.51    (![A:$i,B:$i,C:$i,D:$i]:
% 37.27/37.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 37.27/37.51       ( ![E:$i]:
% 37.27/37.51         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 37.27/37.51  thf('5', plain,
% 37.27/37.51      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 37.27/37.51         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 37.27/37.51          | (r2_hidden @ X11 @ X15)
% 37.27/37.51          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 37.27/37.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 37.27/37.51  thf('6', plain,
% 37.27/37.51      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 37.27/37.51         ((r2_hidden @ X11 @ (k1_enumset1 @ X14 @ X13 @ X12))
% 37.27/37.51          | (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14))),
% 37.27/37.51      inference('simplify', [status(thm)], ['5'])).
% 37.27/37.51  thf('7', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 37.27/37.51          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 37.27/37.51      inference('sup+', [status(thm)], ['4', '6'])).
% 37.27/37.51  thf('8', plain,
% 37.27/37.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 37.27/37.51         (((X7) != (X6)) | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 37.27/37.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 37.27/37.51  thf('9', plain,
% 37.27/37.51      (![X6 : $i, X8 : $i, X9 : $i]: ~ (zip_tseitin_0 @ X6 @ X8 @ X9 @ X6)),
% 37.27/37.51      inference('simplify', [status(thm)], ['8'])).
% 37.27/37.51  thf('10', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 37.27/37.51      inference('sup-', [status(thm)], ['7', '9'])).
% 37.27/37.51  thf('11', plain,
% 37.27/37.51      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 37.27/37.51          = (k2_tarski @ sk_A @ sk_B)))
% 37.27/37.51         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 37.27/37.51                = (k2_tarski @ sk_A @ sk_B))))),
% 37.27/37.51      inference('split', [status(esa)], ['2'])).
% 37.27/37.51  thf(d5_xboole_0, axiom,
% 37.27/37.51    (![A:$i,B:$i,C:$i]:
% 37.27/37.51     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 37.27/37.51       ( ![D:$i]:
% 37.27/37.51         ( ( r2_hidden @ D @ C ) <=>
% 37.27/37.51           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 37.27/37.51  thf('12', plain,
% 37.27/37.51      (![X1 : $i, X2 : $i, X5 : $i]:
% 37.27/37.51         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 37.27/37.51          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 37.27/37.51          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 37.27/37.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 37.27/37.51  thf('13', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 37.27/37.51          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 37.27/37.51      inference('eq_fact', [status(thm)], ['12'])).
% 37.27/37.51  thf('14', plain,
% 37.27/37.51      (![X1 : $i, X2 : $i, X5 : $i]:
% 37.27/37.51         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 37.27/37.51          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 37.27/37.51          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 37.27/37.51          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 37.27/37.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 37.27/37.51  thf('15', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 37.27/37.51          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 37.27/37.51          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 37.27/37.51          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 37.27/37.51      inference('sup-', [status(thm)], ['13', '14'])).
% 37.27/37.51  thf('16', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 37.27/37.51          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 37.27/37.51          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 37.27/37.51      inference('simplify', [status(thm)], ['15'])).
% 37.27/37.51  thf('17', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 37.27/37.51          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 37.27/37.51      inference('eq_fact', [status(thm)], ['12'])).
% 37.27/37.51  thf('18', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 37.27/37.51          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 37.27/37.51      inference('clc', [status(thm)], ['16', '17'])).
% 37.27/37.51  thf('19', plain,
% 37.27/37.51      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 37.27/37.51         (~ (r2_hidden @ X4 @ X3)
% 37.27/37.51          | (r2_hidden @ X4 @ X1)
% 37.27/37.51          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 37.27/37.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 37.27/37.51  thf('20', plain,
% 37.27/37.51      (![X1 : $i, X2 : $i, X4 : $i]:
% 37.27/37.51         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 37.27/37.51      inference('simplify', [status(thm)], ['19'])).
% 37.27/37.51  thf('21', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 37.27/37.51          | (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X1))),
% 37.27/37.51      inference('sup-', [status(thm)], ['18', '20'])).
% 37.27/37.51  thf('22', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 37.27/37.51          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 37.27/37.51      inference('clc', [status(thm)], ['16', '17'])).
% 37.27/37.51  thf('23', plain,
% 37.27/37.51      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 37.27/37.51         (~ (r2_hidden @ X4 @ X3)
% 37.27/37.51          | ~ (r2_hidden @ X4 @ X2)
% 37.27/37.51          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 37.27/37.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 37.27/37.51  thf('24', plain,
% 37.27/37.51      (![X1 : $i, X2 : $i, X4 : $i]:
% 37.27/37.51         (~ (r2_hidden @ X4 @ X2)
% 37.27/37.51          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 37.27/37.51      inference('simplify', [status(thm)], ['23'])).
% 37.27/37.51  thf('25', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 37.27/37.51          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 37.27/37.51      inference('sup-', [status(thm)], ['22', '24'])).
% 37.27/37.51  thf('26', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         (((X1) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))
% 37.27/37.51          | ((X1) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))))),
% 37.27/37.51      inference('sup-', [status(thm)], ['21', '25'])).
% 37.27/37.51  thf('27', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         ((X1) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 37.27/37.51      inference('simplify', [status(thm)], ['26'])).
% 37.27/37.51  thf('28', plain,
% 37.27/37.51      (((r2_hidden @ sk_B @ sk_C)
% 37.27/37.51        | (r2_hidden @ sk_A @ sk_C)
% 37.27/37.51        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 37.27/37.51            != (k2_tarski @ sk_A @ sk_B)))),
% 37.27/37.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.27/37.51  thf('29', plain,
% 37.27/37.51      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 37.27/37.51      inference('split', [status(esa)], ['28'])).
% 37.27/37.51  thf('30', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 37.27/37.51         (~ (r2_hidden @ X0 @ X1)
% 37.27/37.51          | (r2_hidden @ X0 @ X2)
% 37.27/37.51          | (r2_hidden @ X0 @ X3)
% 37.27/37.51          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 37.27/37.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 37.27/37.51  thf('31', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 37.27/37.51          | (r2_hidden @ X0 @ X2)
% 37.27/37.51          | ~ (r2_hidden @ X0 @ X1))),
% 37.27/37.51      inference('simplify', [status(thm)], ['30'])).
% 37.27/37.51  thf('32', plain,
% 37.27/37.51      ((![X0 : $i]:
% 37.27/37.51          ((r2_hidden @ sk_A @ X0)
% 37.27/37.51           | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_C @ X0))))
% 37.27/37.51         <= (((r2_hidden @ sk_A @ sk_C)))),
% 37.27/37.51      inference('sup-', [status(thm)], ['29', '31'])).
% 37.27/37.51  thf('33', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 37.27/37.51          | (r2_hidden @ X0 @ X2)
% 37.27/37.51          | ~ (r2_hidden @ X0 @ X1))),
% 37.27/37.51      inference('simplify', [status(thm)], ['30'])).
% 37.27/37.51  thf('34', plain,
% 37.27/37.51      ((![X0 : $i, X1 : $i]:
% 37.27/37.51          ((r2_hidden @ sk_A @ X0)
% 37.27/37.51           | (r2_hidden @ sk_A @ X1)
% 37.27/37.51           | (r2_hidden @ sk_A @ (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ X0) @ X1))))
% 37.27/37.51         <= (((r2_hidden @ sk_A @ sk_C)))),
% 37.27/37.51      inference('sup-', [status(thm)], ['32', '33'])).
% 37.27/37.51  thf('35', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 37.27/37.51          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 37.27/37.51      inference('eq_fact', [status(thm)], ['12'])).
% 37.27/37.51  thf('36', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 37.27/37.51          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 37.27/37.51      inference('sup-', [status(thm)], ['22', '24'])).
% 37.27/37.51  thf('37', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         (((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 37.27/37.51          | ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 37.27/37.51      inference('sup-', [status(thm)], ['35', '36'])).
% 37.27/37.51  thf('38', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 37.27/37.51      inference('simplify', [status(thm)], ['37'])).
% 37.27/37.51  thf('39', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 37.27/37.51          | (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X1))),
% 37.27/37.51      inference('sup-', [status(thm)], ['18', '20'])).
% 37.27/37.51  thf('40', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 37.27/37.51      inference('simplify', [status(thm)], ['37'])).
% 37.27/37.51  thf('41', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 37.27/37.51          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 37.27/37.51      inference('eq_fact', [status(thm)], ['12'])).
% 37.27/37.51  thf('42', plain,
% 37.27/37.51      (![X1 : $i, X2 : $i, X4 : $i]:
% 37.27/37.51         (~ (r2_hidden @ X4 @ X2)
% 37.27/37.51          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 37.27/37.51      inference('simplify', [status(thm)], ['23'])).
% 37.27/37.51  thf('43', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         (((k4_xboole_0 @ X1 @ X0)
% 37.27/37.51            = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 37.27/37.51          | ~ (r2_hidden @ 
% 37.27/37.51               (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 37.27/37.51               X0))),
% 37.27/37.51      inference('sup-', [status(thm)], ['41', '42'])).
% 37.27/37.51  thf('44', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         (~ (r2_hidden @ 
% 37.27/37.51             (sk_D @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2 @ X0) @ 
% 37.27/37.51             (k4_xboole_0 @ X1 @ X0))
% 37.27/37.51          | ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 37.27/37.51              = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 37.27/37.51                 X2)))),
% 37.27/37.51      inference('sup-', [status(thm)], ['40', '43'])).
% 37.27/37.51  thf('45', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 37.27/37.51      inference('simplify', [status(thm)], ['37'])).
% 37.27/37.51  thf('46', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 37.27/37.51      inference('simplify', [status(thm)], ['37'])).
% 37.27/37.51  thf('47', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 37.27/37.51      inference('simplify', [status(thm)], ['37'])).
% 37.27/37.51  thf('48', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         (~ (r2_hidden @ (sk_D @ X0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 37.27/37.51          | ((X0) = (k4_xboole_0 @ X0 @ X2)))),
% 37.27/37.51      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 37.27/37.51  thf('49', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         (((X0)
% 37.27/37.51            = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))
% 37.27/37.51          | ((X0)
% 37.27/37.51              = (k4_xboole_0 @ X0 @ 
% 37.27/37.51                 (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))))),
% 37.27/37.51      inference('sup-', [status(thm)], ['39', '48'])).
% 37.27/37.51  thf('50', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         ((X0)
% 37.27/37.51           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 37.27/37.51      inference('simplify', [status(thm)], ['49'])).
% 37.27/37.51  thf('51', plain,
% 37.27/37.51      (![X1 : $i, X2 : $i, X4 : $i]:
% 37.27/37.51         (~ (r2_hidden @ X4 @ X2)
% 37.27/37.51          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 37.27/37.51      inference('simplify', [status(thm)], ['23'])).
% 37.27/37.51  thf('52', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 37.27/37.51         (~ (r2_hidden @ X3 @ X0)
% 37.27/37.51          | ~ (r2_hidden @ X3 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)))),
% 37.27/37.51      inference('sup-', [status(thm)], ['50', '51'])).
% 37.27/37.51  thf('53', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 37.27/37.51         (~ (r2_hidden @ X3 @ (k4_xboole_0 @ X0 @ X1))
% 37.27/37.51          | ~ (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ X0)))),
% 37.27/37.51      inference('sup-', [status(thm)], ['38', '52'])).
% 37.27/37.51  thf('54', plain,
% 37.27/37.51      ((![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51          ((r2_hidden @ sk_A @ X0)
% 37.27/37.51           | (r2_hidden @ sk_A @ X1)
% 37.27/37.51           | ~ (r2_hidden @ sk_A @ 
% 37.27/37.51                (k4_xboole_0 @ X2 @ (k4_xboole_0 @ sk_C @ X1)))))
% 37.27/37.51         <= (((r2_hidden @ sk_A @ sk_C)))),
% 37.27/37.51      inference('sup-', [status(thm)], ['34', '53'])).
% 37.27/37.51  thf('55', plain,
% 37.27/37.51      ((![X0 : $i, X1 : $i]:
% 37.27/37.51          (~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ sk_C @ X0)))
% 37.27/37.51           | (r2_hidden @ sk_A @ X0)))
% 37.27/37.51         <= (((r2_hidden @ sk_A @ sk_C)))),
% 37.27/37.51      inference('condensation', [status(thm)], ['54'])).
% 37.27/37.51  thf('56', plain,
% 37.27/37.51      ((![X0 : $i, X1 : $i]:
% 37.27/37.51          (~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X1 @ sk_C))
% 37.27/37.51           | (r2_hidden @ sk_A @ (k4_xboole_0 @ X0 @ X0))))
% 37.27/37.51         <= (((r2_hidden @ sk_A @ sk_C)))),
% 37.27/37.51      inference('sup-', [status(thm)], ['27', '55'])).
% 37.27/37.51  thf('57', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         ((X1) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 37.27/37.51      inference('simplify', [status(thm)], ['26'])).
% 37.27/37.51  thf('58', plain,
% 37.27/37.51      (![X1 : $i, X2 : $i, X4 : $i]:
% 37.27/37.51         (~ (r2_hidden @ X4 @ X2)
% 37.27/37.51          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 37.27/37.51      inference('simplify', [status(thm)], ['23'])).
% 37.27/37.51  thf('59', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         (~ (r2_hidden @ X2 @ X0)
% 37.27/37.51          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X1)))),
% 37.27/37.51      inference('sup-', [status(thm)], ['57', '58'])).
% 37.27/37.51  thf('60', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 37.27/37.51      inference('condensation', [status(thm)], ['59'])).
% 37.27/37.51  thf('61', plain,
% 37.27/37.51      ((![X1 : $i]: ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X1 @ sk_C)))
% 37.27/37.51         <= (((r2_hidden @ sk_A @ sk_C)))),
% 37.27/37.51      inference('clc', [status(thm)], ['56', '60'])).
% 37.27/37.51  thf('62', plain,
% 37.27/37.51      ((~ (r2_hidden @ sk_A @ (k2_tarski @ sk_A @ sk_B)))
% 37.27/37.51         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 37.27/37.51                = (k2_tarski @ sk_A @ sk_B))) & 
% 37.27/37.51             ((r2_hidden @ sk_A @ sk_C)))),
% 37.27/37.51      inference('sup-', [status(thm)], ['11', '61'])).
% 37.27/37.51  thf('63', plain,
% 37.27/37.51      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 37.27/37.51       ~
% 37.27/37.51       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 37.27/37.51          = (k2_tarski @ sk_A @ sk_B)))),
% 37.27/37.51      inference('sup-', [status(thm)], ['10', '62'])).
% 37.27/37.51  thf('64', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 37.27/37.51          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 37.27/37.51      inference('sup+', [status(thm)], ['4', '6'])).
% 37.27/37.51  thf('65', plain,
% 37.27/37.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 37.27/37.51         (((X7) != (X8)) | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 37.27/37.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 37.27/37.51  thf('66', plain,
% 37.27/37.51      (![X6 : $i, X8 : $i, X9 : $i]: ~ (zip_tseitin_0 @ X8 @ X8 @ X9 @ X6)),
% 37.27/37.51      inference('simplify', [status(thm)], ['65'])).
% 37.27/37.51  thf('67', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 37.27/37.51      inference('sup-', [status(thm)], ['64', '66'])).
% 37.27/37.51  thf('68', plain,
% 37.27/37.51      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 37.27/37.51          = (k2_tarski @ sk_A @ sk_B)))
% 37.27/37.51         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 37.27/37.51                = (k2_tarski @ sk_A @ sk_B))))),
% 37.27/37.51      inference('split', [status(esa)], ['2'])).
% 37.27/37.51  thf('69', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         ((X1) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 37.27/37.51      inference('simplify', [status(thm)], ['26'])).
% 37.27/37.51  thf('70', plain,
% 37.27/37.51      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 37.27/37.51      inference('split', [status(esa)], ['28'])).
% 37.27/37.51  thf('71', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 37.27/37.51          | (r2_hidden @ X0 @ X2)
% 37.27/37.51          | ~ (r2_hidden @ X0 @ X1))),
% 37.27/37.51      inference('simplify', [status(thm)], ['30'])).
% 37.27/37.51  thf('72', plain,
% 37.27/37.51      ((![X0 : $i]:
% 37.27/37.51          ((r2_hidden @ sk_B @ X0)
% 37.27/37.51           | (r2_hidden @ sk_B @ (k4_xboole_0 @ sk_C @ X0))))
% 37.27/37.51         <= (((r2_hidden @ sk_B @ sk_C)))),
% 37.27/37.51      inference('sup-', [status(thm)], ['70', '71'])).
% 37.27/37.51  thf('73', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 37.27/37.51          | (r2_hidden @ X0 @ X2)
% 37.27/37.51          | ~ (r2_hidden @ X0 @ X1))),
% 37.27/37.51      inference('simplify', [status(thm)], ['30'])).
% 37.27/37.51  thf('74', plain,
% 37.27/37.51      ((![X0 : $i, X1 : $i]:
% 37.27/37.51          ((r2_hidden @ sk_B @ X0)
% 37.27/37.51           | (r2_hidden @ sk_B @ X1)
% 37.27/37.51           | (r2_hidden @ sk_B @ (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ X0) @ X1))))
% 37.27/37.51         <= (((r2_hidden @ sk_B @ sk_C)))),
% 37.27/37.51      inference('sup-', [status(thm)], ['72', '73'])).
% 37.27/37.51  thf('75', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 37.27/37.51         (~ (r2_hidden @ X3 @ (k4_xboole_0 @ X0 @ X1))
% 37.27/37.51          | ~ (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ X0)))),
% 37.27/37.51      inference('sup-', [status(thm)], ['38', '52'])).
% 37.27/37.51  thf('76', plain,
% 37.27/37.51      ((![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51          ((r2_hidden @ sk_B @ X0)
% 37.27/37.51           | (r2_hidden @ sk_B @ X1)
% 37.27/37.51           | ~ (r2_hidden @ sk_B @ 
% 37.27/37.51                (k4_xboole_0 @ X2 @ (k4_xboole_0 @ sk_C @ X1)))))
% 37.27/37.51         <= (((r2_hidden @ sk_B @ sk_C)))),
% 37.27/37.51      inference('sup-', [status(thm)], ['74', '75'])).
% 37.27/37.51  thf('77', plain,
% 37.27/37.51      ((![X0 : $i, X1 : $i]:
% 37.27/37.51          (~ (r2_hidden @ sk_B @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ sk_C @ X0)))
% 37.27/37.51           | (r2_hidden @ sk_B @ X0)))
% 37.27/37.51         <= (((r2_hidden @ sk_B @ sk_C)))),
% 37.27/37.51      inference('condensation', [status(thm)], ['76'])).
% 37.27/37.51  thf('78', plain,
% 37.27/37.51      ((![X0 : $i, X1 : $i]:
% 37.27/37.51          (~ (r2_hidden @ sk_B @ (k4_xboole_0 @ X1 @ sk_C))
% 37.27/37.51           | (r2_hidden @ sk_B @ (k4_xboole_0 @ X0 @ X0))))
% 37.27/37.51         <= (((r2_hidden @ sk_B @ sk_C)))),
% 37.27/37.51      inference('sup-', [status(thm)], ['69', '77'])).
% 37.27/37.51  thf('79', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 37.27/37.51      inference('condensation', [status(thm)], ['59'])).
% 37.27/37.51  thf('80', plain,
% 37.27/37.51      ((![X1 : $i]: ~ (r2_hidden @ sk_B @ (k4_xboole_0 @ X1 @ sk_C)))
% 37.27/37.51         <= (((r2_hidden @ sk_B @ sk_C)))),
% 37.27/37.51      inference('clc', [status(thm)], ['78', '79'])).
% 37.27/37.51  thf('81', plain,
% 37.27/37.51      ((~ (r2_hidden @ sk_B @ (k2_tarski @ sk_A @ sk_B)))
% 37.27/37.51         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 37.27/37.51                = (k2_tarski @ sk_A @ sk_B))) & 
% 37.27/37.51             ((r2_hidden @ sk_B @ sk_C)))),
% 37.27/37.51      inference('sup-', [status(thm)], ['68', '80'])).
% 37.27/37.51  thf('82', plain,
% 37.27/37.51      (~ ((r2_hidden @ sk_B @ sk_C)) | 
% 37.27/37.51       ~
% 37.27/37.51       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 37.27/37.51          = (k2_tarski @ sk_A @ sk_B)))),
% 37.27/37.51      inference('sup-', [status(thm)], ['67', '81'])).
% 37.27/37.51  thf('83', plain,
% 37.27/37.51      (~
% 37.27/37.51       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 37.27/37.51          = (k2_tarski @ sk_A @ sk_B))) | 
% 37.27/37.51       ((r2_hidden @ sk_B @ sk_C)) | ((r2_hidden @ sk_A @ sk_C))),
% 37.27/37.51      inference('split', [status(esa)], ['28'])).
% 37.27/37.51  thf('84', plain,
% 37.27/37.51      (~ ((r2_hidden @ sk_B @ sk_C)) | 
% 37.27/37.51       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 37.27/37.51          = (k2_tarski @ sk_A @ sk_B)))),
% 37.27/37.51      inference('split', [status(esa)], ['0'])).
% 37.27/37.51  thf('85', plain, (~ ((r2_hidden @ sk_B @ sk_C))),
% 37.27/37.51      inference('sat_resolution*', [status(thm)], ['3', '63', '82', '83', '84'])).
% 37.27/37.51  thf('86', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 37.27/37.51      inference('simpl_trail', [status(thm)], ['1', '85'])).
% 37.27/37.51  thf('87', plain,
% 37.27/37.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 37.27/37.51         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 37.27/37.51          | ((X7) = (X8))
% 37.27/37.51          | ((X7) = (X9))
% 37.27/37.51          | ((X7) = (X10)))),
% 37.27/37.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 37.27/37.51  thf('88', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 37.27/37.51          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 37.27/37.51      inference('clc', [status(thm)], ['16', '17'])).
% 37.27/37.51  thf('89', plain,
% 37.27/37.51      (![X18 : $i, X19 : $i]:
% 37.27/37.51         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 37.27/37.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 37.27/37.51  thf('90', plain,
% 37.27/37.51      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 37.27/37.51         (~ (r2_hidden @ X16 @ X15)
% 37.27/37.51          | ~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 37.27/37.51          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 37.27/37.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 37.27/37.51  thf('91', plain,
% 37.27/37.51      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 37.27/37.51         (~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 37.27/37.51          | ~ (r2_hidden @ X16 @ (k1_enumset1 @ X14 @ X13 @ X12)))),
% 37.27/37.51      inference('simplify', [status(thm)], ['90'])).
% 37.27/37.51  thf('92', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 37.27/37.51          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 37.27/37.51      inference('sup-', [status(thm)], ['89', '91'])).
% 37.27/37.51  thf('93', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         (((X2) = (k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))
% 37.27/37.51          | ~ (zip_tseitin_0 @ (sk_D @ X2 @ (k2_tarski @ X1 @ X0) @ X2) @ X0 @ 
% 37.27/37.51               X1 @ X1))),
% 37.27/37.51      inference('sup-', [status(thm)], ['88', '92'])).
% 37.27/37.51  thf('94', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         (((sk_D @ X2 @ (k2_tarski @ X0 @ X1) @ X2) = (X0))
% 37.27/37.51          | ((sk_D @ X2 @ (k2_tarski @ X0 @ X1) @ X2) = (X0))
% 37.27/37.51          | ((sk_D @ X2 @ (k2_tarski @ X0 @ X1) @ X2) = (X1))
% 37.27/37.51          | ((X2) = (k4_xboole_0 @ X2 @ (k2_tarski @ X0 @ X1))))),
% 37.27/37.51      inference('sup-', [status(thm)], ['87', '93'])).
% 37.27/37.51  thf('95', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         (((X2) = (k4_xboole_0 @ X2 @ (k2_tarski @ X0 @ X1)))
% 37.27/37.51          | ((sk_D @ X2 @ (k2_tarski @ X0 @ X1) @ X2) = (X1))
% 37.27/37.51          | ((sk_D @ X2 @ (k2_tarski @ X0 @ X1) @ X2) = (X0)))),
% 37.27/37.51      inference('simplify', [status(thm)], ['94'])).
% 37.27/37.51  thf('96', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 37.27/37.51          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 37.27/37.51      inference('eq_fact', [status(thm)], ['12'])).
% 37.27/37.51  thf('97', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         ((r2_hidden @ X0 @ X1)
% 37.27/37.51          | ((sk_D @ X1 @ (k2_tarski @ X2 @ X0) @ X1) = (X2))
% 37.27/37.51          | ((X1) = (k4_xboole_0 @ X1 @ (k2_tarski @ X2 @ X0)))
% 37.27/37.51          | ((X1) = (k4_xboole_0 @ X1 @ (k2_tarski @ X2 @ X0))))),
% 37.27/37.51      inference('sup+', [status(thm)], ['95', '96'])).
% 37.27/37.51  thf('98', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         (((X1) = (k4_xboole_0 @ X1 @ (k2_tarski @ X2 @ X0)))
% 37.27/37.51          | ((sk_D @ X1 @ (k2_tarski @ X2 @ X0) @ X1) = (X2))
% 37.27/37.51          | (r2_hidden @ X0 @ X1))),
% 37.27/37.51      inference('simplify', [status(thm)], ['97'])).
% 37.27/37.51  thf('99', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 37.27/37.51          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 37.27/37.51      inference('eq_fact', [status(thm)], ['12'])).
% 37.27/37.51  thf('100', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         ((r2_hidden @ X0 @ X1)
% 37.27/37.51          | (r2_hidden @ X2 @ X1)
% 37.27/37.51          | ((X1) = (k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X2)))
% 37.27/37.51          | ((X1) = (k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X2))))),
% 37.27/37.51      inference('sup+', [status(thm)], ['98', '99'])).
% 37.27/37.51  thf('101', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         (((X1) = (k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X2)))
% 37.27/37.51          | (r2_hidden @ X2 @ X1)
% 37.27/37.51          | (r2_hidden @ X0 @ X1))),
% 37.27/37.51      inference('simplify', [status(thm)], ['100'])).
% 37.27/37.51  thf('102', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i]:
% 37.27/37.51         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 37.27/37.51      inference('simplify', [status(thm)], ['37'])).
% 37.27/37.51  thf('103', plain,
% 37.27/37.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.27/37.51         (((k2_tarski @ X2 @ X1) = (k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0))
% 37.27/37.51          | (r2_hidden @ X2 @ X0)
% 37.27/37.51          | (r2_hidden @ X1 @ X0))),
% 37.27/37.51      inference('sup+', [status(thm)], ['101', '102'])).
% 37.27/37.51  thf('104', plain,
% 37.27/37.51      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 37.27/37.51          != (k2_tarski @ sk_A @ sk_B)))
% 37.27/37.51         <= (~
% 37.27/37.51             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 37.27/37.51                = (k2_tarski @ sk_A @ sk_B))))),
% 37.27/37.51      inference('split', [status(esa)], ['28'])).
% 37.27/37.51  thf('105', plain,
% 37.27/37.51      (~
% 37.27/37.51       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 37.27/37.51          = (k2_tarski @ sk_A @ sk_B)))),
% 37.27/37.51      inference('sat_resolution*', [status(thm)], ['3', '63', '82', '83'])).
% 37.27/37.51  thf('106', plain,
% 37.27/37.51      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 37.27/37.51         != (k2_tarski @ sk_A @ sk_B))),
% 37.27/37.51      inference('simpl_trail', [status(thm)], ['104', '105'])).
% 37.27/37.51  thf('107', plain,
% 37.27/37.51      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 37.27/37.51        | (r2_hidden @ sk_B @ sk_C)
% 37.27/37.51        | (r2_hidden @ sk_A @ sk_C))),
% 37.27/37.51      inference('sup-', [status(thm)], ['103', '106'])).
% 37.27/37.51  thf('108', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 37.27/37.51      inference('simplify', [status(thm)], ['107'])).
% 37.27/37.51  thf('109', plain,
% 37.27/37.51      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 37.27/37.51      inference('split', [status(esa)], ['2'])).
% 37.27/37.51  thf('110', plain, (~ ((r2_hidden @ sk_A @ sk_C))),
% 37.27/37.51      inference('sat_resolution*', [status(thm)], ['3', '63'])).
% 37.27/37.51  thf('111', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 37.27/37.51      inference('simpl_trail', [status(thm)], ['109', '110'])).
% 37.27/37.51  thf('112', plain, ((r2_hidden @ sk_B @ sk_C)),
% 37.27/37.51      inference('clc', [status(thm)], ['108', '111'])).
% 37.27/37.51  thf('113', plain, ($false), inference('demod', [status(thm)], ['86', '112'])).
% 37.27/37.51  
% 37.27/37.51  % SZS output end Refutation
% 37.27/37.51  
% 37.37/37.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

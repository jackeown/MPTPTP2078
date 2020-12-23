%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Rs9h1T6Cxn

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 494 expanded)
%              Number of leaves         :   20 ( 135 expanded)
%              Depth                    :   22
%              Number of atoms          :  759 (5548 expanded)
%              Number of equality atoms :  138 (1031 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t130_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != k1_xboole_0 )
       => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
           != k1_xboole_0 )
          & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_zfmisc_1])).

thf('1',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X19 @ X18 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X23 ) )
        = ( k1_tarski @ X22 ) )
      | ( X22 = X23 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t73_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X24 @ X25 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X24 @ X26 ) @ X25 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t73_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( X0 = X1 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r2_hidden @ sk_B @ ( k1_tarski @ X0 ) )
        | ( sk_B = X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( sk_B = X0 )
        | ( r2_hidden @ sk_B @ ( k1_tarski @ X0 ) ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X19 @ X18 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('18',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( X0 = X1 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r2_hidden @ sk_B @ ( k1_tarski @ X0 ) )
        | ( sk_B = X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( sk_B = X0 )
        | ( r2_hidden @ sk_B @ ( k1_tarski @ X0 ) ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( sk_B = X0 )
        | ~ ( zip_tseitin_0 @ sk_B @ X0 @ X0 @ X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( sk_B = X0 )
        | ( sk_B = X0 )
        | ( sk_B = X0 )
        | ( sk_B = X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','31'])).

thf('33',plain,
    ( ! [X0: $i] : ( sk_B = X0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('35',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22 != X21 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X21 ) )
       != ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('36',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X21 ) )
     != ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('39',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('40',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ! [X0: $i] : ( sk_B = X0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('42',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ! [X0: $i] : ( X0 != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('46',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ( r2_hidden @ sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference(simpl_trail,[status(thm)],['14','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ~ ( zip_tseitin_0 @ sk_B @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ( sk_B = X0 )
      | ( sk_B = X0 )
      | ( sk_B = X0 ) ) ),
    inference('sup-',[status(thm)],['0','49'])).

thf('51',plain,(
    ! [X0: $i] : ( sk_B = X0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('53',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X21 ) )
     != ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('54',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('56',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('57',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['44','45'])).

thf('59',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] : ( sk_B = X0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('61',plain,(
    sk_B != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] : ( X0 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','61'])).

thf('63',plain,(
    $false ),
    inference(simplify,[status(thm)],['62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Rs9h1T6Cxn
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:09:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 139 iterations in 0.067s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(d1_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.53       ( ![E:$i]:
% 0.20/0.53         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.53           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, axiom,
% 0.20/0.53    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.53     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.53       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.20/0.53          | ((X1) = (X2))
% 0.20/0.53          | ((X1) = (X3))
% 0.20/0.53          | ((X1) = (X4)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t130_zfmisc_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.53       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_1, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i]:
% 0.20/0.53        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.53          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.20/0.53        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['1'])).
% 0.20/0.53  thf(t113_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i]:
% 0.20/0.53         (((X18) = (k1_xboole_0))
% 0.20/0.53          | ((X19) = (k1_xboole_0))
% 0.20/0.53          | ((k2_zfmisc_1 @ X19 @ X18) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.53         | ((sk_A) = (k1_xboole_0))
% 0.20/0.53         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.53  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf(t69_enumset1, axiom,
% 0.20/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.53  thf('8', plain, (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.53  thf(t20_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.53         ( k1_tarski @ A ) ) <=>
% 0.20/0.53       ( ( A ) != ( B ) ) ))).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X23))
% 0.20/0.53            = (k1_tarski @ X22))
% 0.20/0.53          | ((X22) = (X23)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1))
% 0.20/0.53            = (k1_tarski @ X0))
% 0.20/0.53          | ((X0) = (X1)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf(t73_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.53       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.53         ((r2_hidden @ X24 @ X25)
% 0.20/0.53          | ((k4_xboole_0 @ (k2_tarski @ X24 @ X26) @ X25) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t73_zfmisc_1])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k1_tarski @ X0) != (k1_xboole_0))
% 0.20/0.53          | ((X0) = (X1))
% 0.20/0.53          | (r2_hidden @ X0 @ (k1_tarski @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.53           | (r2_hidden @ sk_B @ (k1_tarski @ X0))
% 0.20/0.53           | ((sk_B) = (X0))))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      ((![X0 : $i]: (((sk_B) = (X0)) | (r2_hidden @ sk_B @ (k1_tarski @ X0))))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.20/0.53          | ((X1) = (X2))
% 0.20/0.53          | ((X1) = (X3))
% 0.20/0.53          | ((X1) = (X4)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['1'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i]:
% 0.20/0.53         (((X18) = (k1_xboole_0))
% 0.20/0.53          | ((X19) = (k1_xboole_0))
% 0.20/0.53          | ((k2_zfmisc_1 @ X19 @ X18) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.53         | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.53         | ((sk_A) = (k1_xboole_0))))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.53  thf('20', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k1_tarski @ X0) != (k1_xboole_0))
% 0.20/0.53          | ((X0) = (X1))
% 0.20/0.53          | (r2_hidden @ X0 @ (k1_tarski @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.53           | (r2_hidden @ sk_B @ (k1_tarski @ X0))
% 0.20/0.53           | ((sk_B) = (X0))))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((![X0 : $i]: (((sk_B) = (X0)) | (r2_hidden @ sk_B @ (k1_tarski @ X0))))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.53  thf(t70_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.53  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_3, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.53       ( ![E:$i]:
% 0.20/0.53         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X10 @ X9)
% 0.20/0.53          | ~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.20/0.53          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.20/0.53         (~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.20/0.53          | ~ (r2_hidden @ X10 @ (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.53          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['26', '28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.53          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['25', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      ((![X0 : $i]: (((sk_B) = (X0)) | ~ (zip_tseitin_0 @ sk_B @ X0 @ X0 @ X0)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (((sk_B) = (X0))
% 0.20/0.53           | ((sk_B) = (X0))
% 0.20/0.53           | ((sk_B) = (X0))
% 0.20/0.53           | ((sk_B) = (X0))))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((![X0 : $i]: ((sk_B) = (X0)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X21 : $i, X22 : $i]:
% 0.20/0.53         (((X22) != (X21))
% 0.20/0.53          | ((k4_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X21))
% 0.20/0.53              != (k1_tarski @ X22)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X21 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X21))
% 0.20/0.53           != (k1_tarski @ X21))),
% 0.20/0.53      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) != (k1_tarski @ sk_B)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['34', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      ((![X0 : $i]: ((sk_B) = (X0)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      ((((sk_B) != (k1_xboole_0)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((![X0 : $i]: ((X0) != (k1_xboole_0)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['33', '42'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))) | 
% 0.20/0.53       (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('split', [status(esa)], ['1'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X0 : $i]: (((sk_B) = (X0)) | (r2_hidden @ sk_B @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['14', '46'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.53          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['25', '29'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (![X0 : $i]: (((sk_B) = (X0)) | ~ (zip_tseitin_0 @ sk_B @ X0 @ X0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((sk_B) = (X0)) | ((sk_B) = (X0)) | ((sk_B) = (X0)) | ((sk_B) = (X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '49'])).
% 0.20/0.53  thf('51', plain, (![X0 : $i]: ((sk_B) = (X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (![X21 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X21))
% 0.20/0.53           != (k1_tarski @ X21))),
% 0.20/0.53      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) != (k1_tarski @ sk_B)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['57', '58'])).
% 0.20/0.53  thf('60', plain, (![X0 : $i]: ((sk_B) = (X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.53  thf('61', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.53  thf('62', plain, (![X0 : $i]: ((X0) != (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['51', '61'])).
% 0.20/0.53  thf('63', plain, ($false), inference('simplify', [status(thm)], ['62'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

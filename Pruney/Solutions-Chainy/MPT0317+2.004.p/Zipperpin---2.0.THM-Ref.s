%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9pkqN4xPjd

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:19 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 266 expanded)
%              Number of leaves         :   23 (  79 expanded)
%              Depth                    :   16
%              Number of atoms          : 1088 (3015 expanded)
%              Number of equality atoms :   81 ( 217 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t129_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
      <=> ( ( r2_hidden @ A @ C )
          & ( B = D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t129_zfmisc_1])).

thf('0',plain,
    ( ( sk_B != sk_D_1 )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) )
    | ( sk_B != sk_D_1 )
    | ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ ( k2_zfmisc_1 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( X7 = X8 )
      | ( X7 = X9 )
      | ( X7 = X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ ( k2_zfmisc_1 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('12',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
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

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ~ ( zip_tseitin_0 @ sk_B @ sk_D_1 @ sk_D_1 @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,
    ( ( ( sk_B = sk_D_1 )
      | ( sk_B = sk_D_1 )
      | ( sk_B = sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,
    ( ( sk_B = sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( sk_B != sk_D_1 )
   <= ( sk_B != sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != sk_D_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B = sk_D_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','8','24'])).

thf('26',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','25'])).

thf('27',plain,
    ( ( sk_B = sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_B = sk_D_1 )
   <= ( sk_B = sk_D_1 ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ( sk_B = sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['27'])).

thf('30',plain,(
    sk_B = sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['2','8','24','29'])).

thf('31',plain,(
    sk_B = sk_D_1 ),
    inference(simpl_trail,[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_B @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','31','32'])).

thf('34',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('36',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('37',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','8','24','36'])).

thf('38',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(simpl_trail,[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('40',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( r2_hidden @ X11 @ X15 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ~ ( zip_tseitin_0 @ X6 @ X8 @ X9 @ X6 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( X7 = X8 )
      | ( X7 = X9 )
      | ( X7 = X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('47',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('48',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('58',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26 != X28 )
      | ~ ( r2_hidden @ X26 @ ( k4_xboole_0 @ X27 @ ( k1_tarski @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('59',plain,(
    ! [X27: $i,X28: $i] :
      ~ ( r2_hidden @ X28 @ ( k4_xboole_0 @ X27 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['61'])).

thf('63',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['61'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('69',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('70',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('73',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('74',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['71','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('79',plain,(
    ! [X27: $i,X28: $i] :
      ~ ( r2_hidden @ X28 @ ( k4_xboole_0 @ X27 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','81'])).

thf('83',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['60','82'])).

thf('84',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','83'])).

thf('85',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ ( k2_zfmisc_1 @ X22 @ X25 ) )
      | ~ ( r2_hidden @ X23 @ X25 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['33','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9pkqN4xPjd
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:50:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.90/1.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.14  % Solved by: fo/fo7.sh
% 0.90/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.14  % done 975 iterations in 0.677s
% 0.90/1.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.14  % SZS output start Refutation
% 0.90/1.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.14  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.90/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.14  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.90/1.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.14  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.14  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.90/1.14  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.90/1.14  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.90/1.14  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.90/1.14  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.90/1.14  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.14  thf(t129_zfmisc_1, conjecture,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.14     ( ( r2_hidden @
% 0.90/1.14         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.90/1.14       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.90/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.14    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.14        ( ( r2_hidden @
% 0.90/1.14            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.90/1.14          ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ) )),
% 0.90/1.14    inference('cnf.neg', [status(esa)], [t129_zfmisc_1])).
% 0.90/1.14  thf('0', plain,
% 0.90/1.14      ((((sk_B) != (sk_D_1))
% 0.90/1.14        | ~ (r2_hidden @ sk_A @ sk_C)
% 0.90/1.14        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('1', plain,
% 0.90/1.14      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))
% 0.90/1.14         <= (~
% 0.90/1.14             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))))),
% 0.90/1.14      inference('split', [status(esa)], ['0'])).
% 0.90/1.14  thf('2', plain,
% 0.90/1.14      (~
% 0.90/1.14       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))) | 
% 0.90/1.14       ~ (((sk_B) = (sk_D_1))) | ~ ((r2_hidden @ sk_A @ sk_C))),
% 0.90/1.14      inference('split', [status(esa)], ['0'])).
% 0.90/1.14  thf('3', plain,
% 0.90/1.14      (((r2_hidden @ sk_A @ sk_C)
% 0.90/1.14        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('4', plain,
% 0.90/1.14      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))
% 0.90/1.14         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))))),
% 0.90/1.14      inference('split', [status(esa)], ['3'])).
% 0.90/1.14  thf(l54_zfmisc_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.14     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.90/1.14       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.90/1.14  thf('5', plain,
% 0.90/1.14      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.90/1.14         ((r2_hidden @ X21 @ X22)
% 0.90/1.14          | ~ (r2_hidden @ (k4_tarski @ X21 @ X23) @ (k2_zfmisc_1 @ X22 @ X24)))),
% 0.90/1.14      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.90/1.14  thf('6', plain,
% 0.90/1.14      (((r2_hidden @ sk_A @ sk_C))
% 0.90/1.14         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['4', '5'])).
% 0.90/1.14  thf('7', plain,
% 0.90/1.14      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.90/1.14      inference('split', [status(esa)], ['0'])).
% 0.90/1.14  thf('8', plain,
% 0.90/1.14      (((r2_hidden @ sk_A @ sk_C)) | 
% 0.90/1.14       ~
% 0.90/1.14       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['6', '7'])).
% 0.90/1.14  thf(d1_enumset1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.14     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.90/1.14       ( ![E:$i]:
% 0.90/1.14         ( ( r2_hidden @ E @ D ) <=>
% 0.90/1.14           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.90/1.14  thf(zf_stmt_1, axiom,
% 0.90/1.14    (![E:$i,C:$i,B:$i,A:$i]:
% 0.90/1.14     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.90/1.14       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.90/1.14  thf('9', plain,
% 0.90/1.14      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.90/1.14         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.90/1.14          | ((X7) = (X8))
% 0.90/1.14          | ((X7) = (X9))
% 0.90/1.14          | ((X7) = (X10)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.14  thf('10', plain,
% 0.90/1.14      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))
% 0.90/1.14         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))))),
% 0.90/1.14      inference('split', [status(esa)], ['3'])).
% 0.90/1.14  thf('11', plain,
% 0.90/1.14      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.90/1.14         ((r2_hidden @ X23 @ X24)
% 0.90/1.14          | ~ (r2_hidden @ (k4_tarski @ X21 @ X23) @ (k2_zfmisc_1 @ X22 @ X24)))),
% 0.90/1.14      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.90/1.14  thf('12', plain,
% 0.90/1.14      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D_1)))
% 0.90/1.14         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['10', '11'])).
% 0.90/1.14  thf(t69_enumset1, axiom,
% 0.90/1.14    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.90/1.14  thf('13', plain,
% 0.90/1.14      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.90/1.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.90/1.14  thf(t70_enumset1, axiom,
% 0.90/1.14    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.90/1.14  thf('14', plain,
% 0.90/1.14      (![X19 : $i, X20 : $i]:
% 0.90/1.14         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.90/1.14      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.90/1.14  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.90/1.14  thf(zf_stmt_3, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.14     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.90/1.14       ( ![E:$i]:
% 0.90/1.14         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.90/1.14  thf('15', plain,
% 0.90/1.14      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X16 @ X15)
% 0.90/1.14          | ~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.90/1.14          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.14  thf('16', plain,
% 0.90/1.14      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.90/1.14         (~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.90/1.14          | ~ (r2_hidden @ X16 @ (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.90/1.14      inference('simplify', [status(thm)], ['15'])).
% 0.90/1.14  thf('17', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.90/1.14          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.90/1.14      inference('sup-', [status(thm)], ['14', '16'])).
% 0.90/1.14  thf('18', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.90/1.14          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['13', '17'])).
% 0.90/1.14  thf('19', plain,
% 0.90/1.14      ((~ (zip_tseitin_0 @ sk_B @ sk_D_1 @ sk_D_1 @ sk_D_1))
% 0.90/1.14         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['12', '18'])).
% 0.90/1.14  thf('20', plain,
% 0.90/1.14      (((((sk_B) = (sk_D_1)) | ((sk_B) = (sk_D_1)) | ((sk_B) = (sk_D_1))))
% 0.90/1.14         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['9', '19'])).
% 0.90/1.14  thf('21', plain,
% 0.90/1.14      ((((sk_B) = (sk_D_1)))
% 0.90/1.14         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))))),
% 0.90/1.14      inference('simplify', [status(thm)], ['20'])).
% 0.90/1.14  thf('22', plain, ((((sk_B) != (sk_D_1))) <= (~ (((sk_B) = (sk_D_1))))),
% 0.90/1.14      inference('split', [status(esa)], ['0'])).
% 0.90/1.14  thf('23', plain,
% 0.90/1.14      ((((sk_B) != (sk_B)))
% 0.90/1.14         <= (~ (((sk_B) = (sk_D_1))) & 
% 0.90/1.14             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.14  thf('24', plain,
% 0.90/1.14      ((((sk_B) = (sk_D_1))) | 
% 0.90/1.14       ~
% 0.90/1.14       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))),
% 0.90/1.14      inference('simplify', [status(thm)], ['23'])).
% 0.90/1.14  thf('25', plain,
% 0.90/1.14      (~
% 0.90/1.14       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))),
% 0.90/1.14      inference('sat_resolution*', [status(thm)], ['2', '8', '24'])).
% 0.90/1.14  thf('26', plain,
% 0.90/1.14      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14          (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))),
% 0.90/1.14      inference('simpl_trail', [status(thm)], ['1', '25'])).
% 0.90/1.14  thf('27', plain,
% 0.90/1.14      ((((sk_B) = (sk_D_1))
% 0.90/1.14        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('28', plain, ((((sk_B) = (sk_D_1))) <= ((((sk_B) = (sk_D_1))))),
% 0.90/1.14      inference('split', [status(esa)], ['27'])).
% 0.90/1.14  thf('29', plain,
% 0.90/1.14      ((((sk_B) = (sk_D_1))) | 
% 0.90/1.14       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))),
% 0.90/1.14      inference('split', [status(esa)], ['27'])).
% 0.90/1.14  thf('30', plain, ((((sk_B) = (sk_D_1)))),
% 0.90/1.14      inference('sat_resolution*', [status(thm)], ['2', '8', '24', '29'])).
% 0.90/1.14  thf('31', plain, (((sk_B) = (sk_D_1))),
% 0.90/1.14      inference('simpl_trail', [status(thm)], ['28', '30'])).
% 0.90/1.14  thf('32', plain,
% 0.90/1.14      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.90/1.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.90/1.14  thf('33', plain,
% 0.90/1.14      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14          (k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_B @ sk_B)))),
% 0.90/1.14      inference('demod', [status(thm)], ['26', '31', '32'])).
% 0.90/1.14  thf('34', plain,
% 0.90/1.14      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.90/1.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.90/1.14  thf('35', plain,
% 0.90/1.14      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.90/1.14      inference('split', [status(esa)], ['3'])).
% 0.90/1.14  thf('36', plain,
% 0.90/1.14      (((r2_hidden @ sk_A @ sk_C)) | 
% 0.90/1.14       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.90/1.14         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))),
% 0.90/1.14      inference('split', [status(esa)], ['3'])).
% 0.90/1.14  thf('37', plain, (((r2_hidden @ sk_A @ sk_C))),
% 0.90/1.14      inference('sat_resolution*', [status(thm)], ['2', '8', '24', '36'])).
% 0.90/1.14  thf('38', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.90/1.14      inference('simpl_trail', [status(thm)], ['35', '37'])).
% 0.90/1.14  thf('39', plain,
% 0.90/1.14      (![X19 : $i, X20 : $i]:
% 0.90/1.14         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.90/1.14      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.90/1.14  thf('40', plain,
% 0.90/1.14      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.90/1.14         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 0.90/1.14          | (r2_hidden @ X11 @ X15)
% 0.90/1.14          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.14  thf('41', plain,
% 0.90/1.14      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.90/1.14         ((r2_hidden @ X11 @ (k1_enumset1 @ X14 @ X13 @ X12))
% 0.90/1.14          | (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14))),
% 0.90/1.14      inference('simplify', [status(thm)], ['40'])).
% 0.90/1.14  thf('42', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.90/1.14          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.90/1.14      inference('sup+', [status(thm)], ['39', '41'])).
% 0.90/1.14  thf('43', plain,
% 0.90/1.14      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.90/1.14         (((X7) != (X6)) | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.14  thf('44', plain,
% 0.90/1.14      (![X6 : $i, X8 : $i, X9 : $i]: ~ (zip_tseitin_0 @ X6 @ X8 @ X9 @ X6)),
% 0.90/1.14      inference('simplify', [status(thm)], ['43'])).
% 0.90/1.14  thf('45', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.90/1.14      inference('sup-', [status(thm)], ['42', '44'])).
% 0.90/1.14  thf('46', plain,
% 0.90/1.14      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.90/1.14         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.90/1.14          | ((X7) = (X8))
% 0.90/1.14          | ((X7) = (X9))
% 0.90/1.14          | ((X7) = (X10)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.14  thf(d5_xboole_0, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.90/1.14       ( ![D:$i]:
% 0.90/1.14         ( ( r2_hidden @ D @ C ) <=>
% 0.90/1.14           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.90/1.14  thf('47', plain,
% 0.90/1.14      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.90/1.14         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.90/1.14          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.90/1.14          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.90/1.14      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.14  thf('48', plain,
% 0.90/1.14      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.90/1.14         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.90/1.14          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.90/1.14          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.90/1.14      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.14  thf('49', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.90/1.14          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.90/1.14          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.90/1.14          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['47', '48'])).
% 0.90/1.14  thf('50', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.90/1.14          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.90/1.14      inference('simplify', [status(thm)], ['49'])).
% 0.90/1.14  thf('51', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.90/1.14          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['13', '17'])).
% 0.90/1.14  thf('52', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 0.90/1.14          | ~ (zip_tseitin_0 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X1) @ X0 @ X0 @ 
% 0.90/1.14               X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['50', '51'])).
% 0.90/1.14  thf('53', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 0.90/1.14          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 0.90/1.14          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 0.90/1.14          | ((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['46', '52'])).
% 0.90/1.14  thf('54', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 0.90/1.14          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0)))),
% 0.90/1.14      inference('simplify', [status(thm)], ['53'])).
% 0.90/1.14  thf('55', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.90/1.14          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.90/1.14      inference('simplify', [status(thm)], ['49'])).
% 0.90/1.14  thf('56', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.90/1.14          | ((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 0.90/1.14          | ((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.90/1.14      inference('sup+', [status(thm)], ['54', '55'])).
% 0.90/1.14  thf('57', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 0.90/1.14          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.90/1.14      inference('simplify', [status(thm)], ['56'])).
% 0.90/1.14  thf(t64_zfmisc_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.90/1.14       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.90/1.14  thf('58', plain,
% 0.90/1.14      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.90/1.14         (((X26) != (X28))
% 0.90/1.14          | ~ (r2_hidden @ X26 @ (k4_xboole_0 @ X27 @ (k1_tarski @ X28))))),
% 0.90/1.14      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.90/1.14  thf('59', plain,
% 0.90/1.14      (![X27 : $i, X28 : $i]:
% 0.90/1.14         ~ (r2_hidden @ X28 @ (k4_xboole_0 @ X27 @ (k1_tarski @ X28)))),
% 0.90/1.14      inference('simplify', [status(thm)], ['58'])).
% 0.90/1.14  thf('60', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X0)))
% 0.90/1.14          | (r2_hidden @ X1 @ (k1_tarski @ X1)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['57', '59'])).
% 0.90/1.14  thf('61', plain,
% 0.90/1.14      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.90/1.14         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.90/1.14          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.90/1.14          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.90/1.14      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.14  thf('62', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.90/1.14          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.90/1.14      inference('eq_fact', [status(thm)], ['61'])).
% 0.90/1.14  thf('63', plain,
% 0.90/1.14      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.90/1.14         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.90/1.14          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.90/1.14          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.90/1.14          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.90/1.14      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.14  thf('64', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.90/1.14          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.90/1.14          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.90/1.14          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['62', '63'])).
% 0.90/1.14  thf('65', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.90/1.14          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.90/1.14          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.90/1.14      inference('simplify', [status(thm)], ['64'])).
% 0.90/1.14  thf('66', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.90/1.14          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.90/1.14      inference('eq_fact', [status(thm)], ['61'])).
% 0.90/1.14  thf('67', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.90/1.14          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 0.90/1.14      inference('clc', [status(thm)], ['65', '66'])).
% 0.90/1.14  thf('68', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.90/1.14          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.90/1.14      inference('simplify', [status(thm)], ['49'])).
% 0.90/1.14  thf('69', plain,
% 0.90/1.14      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X4 @ X3)
% 0.90/1.14          | (r2_hidden @ X4 @ X1)
% 0.90/1.14          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.90/1.14      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.14  thf('70', plain,
% 0.90/1.14      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.90/1.14         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.90/1.14      inference('simplify', [status(thm)], ['69'])).
% 0.90/1.14  thf('71', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         (((k4_xboole_0 @ X1 @ X0) = (k4_xboole_0 @ X2 @ X2))
% 0.90/1.14          | (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X1))),
% 0.90/1.14      inference('sup-', [status(thm)], ['68', '70'])).
% 0.90/1.14  thf('72', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.90/1.14          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.90/1.14      inference('simplify', [status(thm)], ['49'])).
% 0.90/1.14  thf('73', plain,
% 0.90/1.14      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X4 @ X3)
% 0.90/1.14          | ~ (r2_hidden @ X4 @ X2)
% 0.90/1.14          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.90/1.14      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.14  thf('74', plain,
% 0.90/1.14      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X4 @ X2)
% 0.90/1.14          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.90/1.14      inference('simplify', [status(thm)], ['73'])).
% 0.90/1.14  thf('75', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         (((k4_xboole_0 @ X1 @ X0) = (k4_xboole_0 @ X2 @ X2))
% 0.90/1.14          | ~ (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['72', '74'])).
% 0.90/1.14  thf('76', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))
% 0.90/1.14          | ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['71', '75'])).
% 0.90/1.14  thf('77', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))),
% 0.90/1.14      inference('simplify', [status(thm)], ['76'])).
% 0.90/1.14  thf('78', plain,
% 0.90/1.14      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.90/1.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.90/1.14  thf('79', plain,
% 0.90/1.14      (![X27 : $i, X28 : $i]:
% 0.90/1.14         ~ (r2_hidden @ X28 @ (k4_xboole_0 @ X27 @ (k1_tarski @ X28)))),
% 0.90/1.14      inference('simplify', [status(thm)], ['58'])).
% 0.90/1.14  thf('80', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['78', '79'])).
% 0.90/1.14  thf('81', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['77', '80'])).
% 0.90/1.14  thf('82', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((X1) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['67', '81'])).
% 0.90/1.14  thf('83', plain,
% 0.90/1.14      (![X1 : $i, X2 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X1 @ X2) | (r2_hidden @ X1 @ (k1_tarski @ X1)))),
% 0.90/1.14      inference('demod', [status(thm)], ['60', '82'])).
% 0.90/1.14  thf('84', plain, (![X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X1))),
% 0.90/1.14      inference('sup-', [status(thm)], ['45', '83'])).
% 0.90/1.14  thf('85', plain,
% 0.90/1.14      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.90/1.14         ((r2_hidden @ (k4_tarski @ X21 @ X23) @ (k2_zfmisc_1 @ X22 @ X25))
% 0.90/1.14          | ~ (r2_hidden @ X23 @ X25)
% 0.90/1.14          | ~ (r2_hidden @ X21 @ X22))),
% 0.90/1.14      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.90/1.14  thf('86', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X2 @ X1)
% 0.90/1.14          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.90/1.14             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['84', '85'])).
% 0.90/1.14  thf('87', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (r2_hidden @ (k4_tarski @ sk_A @ X0) @ 
% 0.90/1.14          (k2_zfmisc_1 @ sk_C @ (k1_tarski @ X0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['38', '86'])).
% 0.90/1.14  thf('88', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (r2_hidden @ (k4_tarski @ sk_A @ X0) @ 
% 0.90/1.14          (k2_zfmisc_1 @ sk_C @ (k2_tarski @ X0 @ X0)))),
% 0.90/1.14      inference('sup+', [status(thm)], ['34', '87'])).
% 0.90/1.14  thf('89', plain, ($false), inference('demod', [status(thm)], ['33', '88'])).
% 0.90/1.14  
% 0.90/1.14  % SZS output end Refutation
% 0.90/1.14  
% 0.90/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

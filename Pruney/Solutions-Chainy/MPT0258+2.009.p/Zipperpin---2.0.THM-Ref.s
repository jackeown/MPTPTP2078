%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aLBvZmrAU7

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:24 EST 2020

% Result     : Theorem 15.25s
% Output     : Refutation 15.25s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 536 expanded)
%              Number of leaves         :   16 ( 141 expanded)
%              Depth                    :   18
%              Number of atoms          : 1641 (8248 expanded)
%              Number of equality atoms :  134 ( 649 expanded)
%              Maximal formula depth    :   15 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t53_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = ( k2_tarski @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = ( k2_tarski @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != ( k2_tarski @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
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

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) @ X2 ) @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X0 )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X0 )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X1 )
      | ( ( k2_tarski @ X0 @ X1 )
        = ( k3_xboole_0 @ X2 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X0 @ X1 )
        = ( k3_xboole_0 @ X2 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X1 )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( sk_D @ ( k2_tarski @ X2 @ X0 ) @ ( k2_tarski @ X2 @ X0 ) @ X1 )
        = X2 )
      | ( ( k2_tarski @ X2 @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) )
      | ( ( k2_tarski @ X2 @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X2 @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) )
      | ( ( sk_D @ ( k2_tarski @ X2 @ X0 ) @ ( k2_tarski @ X2 @ X0 ) @ X1 )
        = X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k2_tarski @ X0 @ sk_C ) @ ( k2_tarski @ X0 @ sk_C ) @ sk_B )
        = X0 )
      | ( ( k2_tarski @ X0 @ sk_C )
        = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ X0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('21',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X0 @ X1 )
        = ( k3_xboole_0 @ X2 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X1 )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X2 ) @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ( ( k2_tarski @ X0 @ X2 )
        = ( k3_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X2 ) ) )
      | ( ( k2_tarski @ X0 @ X2 )
        = ( k3_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X0 @ X2 )
        = ( k3_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X2 ) ) )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X2 ) @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k2_tarski @ sk_A @ X0 ) @ ( k2_tarski @ sk_A @ X0 ) @ sk_B )
        = X0 )
      | ( ( k2_tarski @ sk_A @ X0 )
        = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,
    ( ( sk_A = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['20','26'])).

thf('28',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) )
    | ( sk_A = sk_C ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('31',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
      = ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ) )
    | ( sk_A = sk_C ) ),
    inference('sup+',[status(thm)],['28','38'])).

thf('40',plain,(
    ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != ( k2_tarski @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
     != ( k2_tarski @ sk_A @ sk_C ) )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) )
    | ( sk_A = sk_C ) ),
    inference(simplify,[status(thm)],['27'])).

thf('43',plain,(
    sk_A = sk_C ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('45',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X8 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X0 @ X1 )
        = ( k3_xboole_0 @ X2 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X1 )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X0 @ X1 ) @ X2 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X2 )
      | ( ( sk_D @ ( k2_tarski @ X2 @ X0 ) @ ( k2_tarski @ X2 @ X0 ) @ X1 )
        = X2 )
      | ( ( k2_tarski @ X2 @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['56'])).

thf('58',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X2 @ X2 )
        = ( k3_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X2 ) ) )
      | ( ( sk_D @ ( k2_tarski @ X2 @ X2 ) @ ( k2_tarski @ X2 @ X2 ) @ X1 )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('65',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('66',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( X3
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(eq_fact,[status(thm)],['67'])).

thf('69',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('70',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X3 @ X2 ) @ X3 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X3 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X2 @ X0 ) @ X0 @ X1 ) @ X0 )
      | ( ( k3_xboole_0 @ X2 @ X0 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['71'])).

thf('73',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X0 )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X2 @ X0 ) @ X0 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X2 @ X0 ) @ X0 @ X1 ) @ X1 )
      | ( ( k3_xboole_0 @ X2 @ X0 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X2 @ X0 ) @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X2 @ X0 ) @ X0 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) )
      | ( ( k3_xboole_0 @ X2 @ X0 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) ) )
      | ( ( k3_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('80',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('81',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('82',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X2 @ X0 ) @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X2 @ X0 ) @ X0 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) )
      | ( ( k3_xboole_0 @ X2 @ X0 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) )
      | ( X1
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X1
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['58','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X0 @ X0 )
        = ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( k2_tarski @ sk_A @ sk_A )
    = ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['55','97'])).

thf('99',plain,(
    sk_A = sk_C ),
    inference(clc,[status(thm)],['41','42'])).

thf('100',plain,(
    ( k2_tarski @ sk_A @ sk_A )
 != ( k2_tarski @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['0','43','98','99'])).

thf('101',plain,(
    $false ),
    inference(simplify,[status(thm)],['100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aLBvZmrAU7
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 15.25/15.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 15.25/15.47  % Solved by: fo/fo7.sh
% 15.25/15.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.25/15.47  % done 5287 iterations in 15.014s
% 15.25/15.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 15.25/15.47  % SZS output start Refutation
% 15.25/15.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 15.25/15.47  thf(sk_C_type, type, sk_C: $i).
% 15.25/15.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 15.25/15.47  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 15.25/15.47  thf(sk_A_type, type, sk_A: $i).
% 15.25/15.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 15.25/15.47  thf(sk_B_type, type, sk_B: $i).
% 15.25/15.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 15.25/15.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 15.25/15.47  thf(t53_zfmisc_1, conjecture,
% 15.25/15.47    (![A:$i,B:$i,C:$i]:
% 15.25/15.47     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 15.25/15.47       ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ))).
% 15.25/15.47  thf(zf_stmt_0, negated_conjecture,
% 15.25/15.47    (~( ![A:$i,B:$i,C:$i]:
% 15.25/15.47        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 15.25/15.47          ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ) )),
% 15.25/15.47    inference('cnf.neg', [status(esa)], [t53_zfmisc_1])).
% 15.25/15.47  thf('0', plain,
% 15.25/15.47      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)
% 15.25/15.47         != (k2_tarski @ sk_A @ sk_C))),
% 15.25/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.25/15.47  thf('1', plain, ((r2_hidden @ sk_C @ sk_B)),
% 15.25/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.25/15.47  thf(d1_enumset1, axiom,
% 15.25/15.47    (![A:$i,B:$i,C:$i,D:$i]:
% 15.25/15.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 15.25/15.47       ( ![E:$i]:
% 15.25/15.47         ( ( r2_hidden @ E @ D ) <=>
% 15.25/15.47           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 15.25/15.47  thf(zf_stmt_1, axiom,
% 15.25/15.47    (![E:$i,C:$i,B:$i,A:$i]:
% 15.25/15.47     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 15.25/15.47       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 15.25/15.47  thf('2', plain,
% 15.25/15.47      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 15.25/15.47         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 15.25/15.47          | ((X9) = (X10))
% 15.25/15.47          | ((X9) = (X11))
% 15.25/15.47          | ((X9) = (X12)))),
% 15.25/15.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.25/15.47  thf(d4_xboole_0, axiom,
% 15.25/15.47    (![A:$i,B:$i,C:$i]:
% 15.25/15.47     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 15.25/15.47       ( ![D:$i]:
% 15.25/15.47         ( ( r2_hidden @ D @ C ) <=>
% 15.25/15.47           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 15.25/15.47  thf('3', plain,
% 15.25/15.47      (![X1 : $i, X2 : $i, X5 : $i]:
% 15.25/15.47         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 15.25/15.47          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 15.25/15.47          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 15.25/15.47      inference('cnf', [status(esa)], [d4_xboole_0])).
% 15.25/15.47  thf('4', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 15.25/15.47          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 15.25/15.47      inference('eq_fact', [status(thm)], ['3'])).
% 15.25/15.47  thf(t70_enumset1, axiom,
% 15.25/15.47    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 15.25/15.47  thf('5', plain,
% 15.25/15.47      (![X20 : $i, X21 : $i]:
% 15.25/15.47         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 15.25/15.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 15.25/15.47  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 15.25/15.47  thf(zf_stmt_3, axiom,
% 15.25/15.47    (![A:$i,B:$i,C:$i,D:$i]:
% 15.25/15.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 15.25/15.47       ( ![E:$i]:
% 15.25/15.47         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 15.25/15.47  thf('6', plain,
% 15.25/15.47      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 15.25/15.47         (~ (r2_hidden @ X18 @ X17)
% 15.25/15.47          | ~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 15.25/15.47          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 15.25/15.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 15.25/15.47  thf('7', plain,
% 15.25/15.47      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 15.25/15.47         (~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 15.25/15.47          | ~ (r2_hidden @ X18 @ (k1_enumset1 @ X16 @ X15 @ X14)))),
% 15.25/15.47      inference('simplify', [status(thm)], ['6'])).
% 15.25/15.47  thf('8', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 15.25/15.47          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 15.25/15.47      inference('sup-', [status(thm)], ['5', '7'])).
% 15.25/15.47  thf('9', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         (((k2_tarski @ X1 @ X0) = (k3_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))
% 15.25/15.47          | ~ (zip_tseitin_0 @ 
% 15.25/15.47               (sk_D @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X1 @ X0) @ X2) @ 
% 15.25/15.47               X0 @ X1 @ X1))),
% 15.25/15.47      inference('sup-', [status(thm)], ['4', '8'])).
% 15.25/15.47  thf('10', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         (((sk_D @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X0 @ X1) @ X2) = (X0))
% 15.25/15.47          | ((sk_D @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X0 @ X1) @ X2) = (X0))
% 15.25/15.47          | ((sk_D @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X0 @ X1) @ X2) = (X1))
% 15.25/15.47          | ((k2_tarski @ X0 @ X1) = (k3_xboole_0 @ X2 @ (k2_tarski @ X0 @ X1))))),
% 15.25/15.47      inference('sup-', [status(thm)], ['2', '9'])).
% 15.25/15.47  thf('11', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         (((k2_tarski @ X0 @ X1) = (k3_xboole_0 @ X2 @ (k2_tarski @ X0 @ X1)))
% 15.25/15.47          | ((sk_D @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X0 @ X1) @ X2) = (X1))
% 15.25/15.47          | ((sk_D @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X0 @ X1) @ X2) = (X0)))),
% 15.25/15.47      inference('simplify', [status(thm)], ['10'])).
% 15.25/15.47  thf('12', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 15.25/15.47          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 15.25/15.47      inference('eq_fact', [status(thm)], ['3'])).
% 15.25/15.47  thf('13', plain,
% 15.25/15.47      (![X1 : $i, X2 : $i, X5 : $i]:
% 15.25/15.47         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 15.25/15.47      inference('cnf', [status(esa)], [d4_xboole_0])).
% 15.25/15.47  thf('14', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 15.25/15.47          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 15.25/15.47      inference('sup-', [status(thm)], ['12', '13'])).
% 15.25/15.47  thf('15', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 15.25/15.47          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 15.25/15.47      inference('simplify', [status(thm)], ['14'])).
% 15.25/15.47  thf('16', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 15.25/15.47          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 15.25/15.47      inference('eq_fact', [status(thm)], ['3'])).
% 15.25/15.47  thf('17', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 15.25/15.47      inference('clc', [status(thm)], ['15', '16'])).
% 15.25/15.47  thf('18', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         (~ (r2_hidden @ X0 @ X1)
% 15.25/15.47          | ((sk_D @ (k2_tarski @ X2 @ X0) @ (k2_tarski @ X2 @ X0) @ X1) = (X2))
% 15.25/15.47          | ((k2_tarski @ X2 @ X0) = (k3_xboole_0 @ X1 @ (k2_tarski @ X2 @ X0)))
% 15.25/15.47          | ((k2_tarski @ X2 @ X0) = (k3_xboole_0 @ X1 @ (k2_tarski @ X2 @ X0))))),
% 15.25/15.47      inference('sup-', [status(thm)], ['11', '17'])).
% 15.25/15.47  thf('19', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         (((k2_tarski @ X2 @ X0) = (k3_xboole_0 @ X1 @ (k2_tarski @ X2 @ X0)))
% 15.25/15.47          | ((sk_D @ (k2_tarski @ X2 @ X0) @ (k2_tarski @ X2 @ X0) @ X1) = (X2))
% 15.25/15.47          | ~ (r2_hidden @ X0 @ X1))),
% 15.25/15.47      inference('simplify', [status(thm)], ['18'])).
% 15.25/15.47  thf('20', plain,
% 15.25/15.47      (![X0 : $i]:
% 15.25/15.47         (((sk_D @ (k2_tarski @ X0 @ sk_C) @ (k2_tarski @ X0 @ sk_C) @ sk_B)
% 15.25/15.47            = (X0))
% 15.25/15.47          | ((k2_tarski @ X0 @ sk_C)
% 15.25/15.47              = (k3_xboole_0 @ sk_B @ (k2_tarski @ X0 @ sk_C))))),
% 15.25/15.47      inference('sup-', [status(thm)], ['1', '19'])).
% 15.25/15.47  thf('21', plain, ((r2_hidden @ sk_A @ sk_B)),
% 15.25/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.25/15.47  thf('22', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         (((k2_tarski @ X0 @ X1) = (k3_xboole_0 @ X2 @ (k2_tarski @ X0 @ X1)))
% 15.25/15.47          | ((sk_D @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X0 @ X1) @ X2) = (X1))
% 15.25/15.47          | ((sk_D @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X0 @ X1) @ X2) = (X0)))),
% 15.25/15.47      inference('simplify', [status(thm)], ['10'])).
% 15.25/15.47  thf('23', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 15.25/15.47      inference('clc', [status(thm)], ['15', '16'])).
% 15.25/15.47  thf('24', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         (~ (r2_hidden @ X0 @ X1)
% 15.25/15.47          | ((sk_D @ (k2_tarski @ X0 @ X2) @ (k2_tarski @ X0 @ X2) @ X1) = (X2))
% 15.25/15.47          | ((k2_tarski @ X0 @ X2) = (k3_xboole_0 @ X1 @ (k2_tarski @ X0 @ X2)))
% 15.25/15.47          | ((k2_tarski @ X0 @ X2) = (k3_xboole_0 @ X1 @ (k2_tarski @ X0 @ X2))))),
% 15.25/15.47      inference('sup-', [status(thm)], ['22', '23'])).
% 15.25/15.47  thf('25', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         (((k2_tarski @ X0 @ X2) = (k3_xboole_0 @ X1 @ (k2_tarski @ X0 @ X2)))
% 15.25/15.47          | ((sk_D @ (k2_tarski @ X0 @ X2) @ (k2_tarski @ X0 @ X2) @ X1) = (X2))
% 15.25/15.47          | ~ (r2_hidden @ X0 @ X1))),
% 15.25/15.47      inference('simplify', [status(thm)], ['24'])).
% 15.25/15.47  thf('26', plain,
% 15.25/15.47      (![X0 : $i]:
% 15.25/15.47         (((sk_D @ (k2_tarski @ sk_A @ X0) @ (k2_tarski @ sk_A @ X0) @ sk_B)
% 15.25/15.47            = (X0))
% 15.25/15.47          | ((k2_tarski @ sk_A @ X0)
% 15.25/15.47              = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ X0))))),
% 15.25/15.47      inference('sup-', [status(thm)], ['21', '25'])).
% 15.25/15.47  thf('27', plain,
% 15.25/15.47      ((((sk_A) = (sk_C))
% 15.25/15.47        | ((k2_tarski @ sk_A @ sk_C)
% 15.25/15.47            = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))
% 15.25/15.47        | ((k2_tarski @ sk_A @ sk_C)
% 15.25/15.47            = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))))),
% 15.25/15.47      inference('sup+', [status(thm)], ['20', '26'])).
% 15.25/15.47  thf('28', plain,
% 15.25/15.47      ((((k2_tarski @ sk_A @ sk_C)
% 15.25/15.47          = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))
% 15.25/15.47        | ((sk_A) = (sk_C)))),
% 15.25/15.47      inference('simplify', [status(thm)], ['27'])).
% 15.25/15.47  thf('29', plain,
% 15.25/15.47      (![X1 : $i, X2 : $i, X5 : $i]:
% 15.25/15.47         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 15.25/15.47          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 15.25/15.47          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 15.25/15.47      inference('cnf', [status(esa)], [d4_xboole_0])).
% 15.25/15.47  thf('30', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 15.25/15.47          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 15.25/15.47      inference('eq_fact', [status(thm)], ['29'])).
% 15.25/15.47  thf('31', plain,
% 15.25/15.47      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 15.25/15.47         (~ (r2_hidden @ X4 @ X3)
% 15.25/15.47          | (r2_hidden @ X4 @ X1)
% 15.25/15.47          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 15.25/15.47      inference('cnf', [status(esa)], [d4_xboole_0])).
% 15.25/15.47  thf('32', plain,
% 15.25/15.47      (![X1 : $i, X2 : $i, X4 : $i]:
% 15.25/15.47         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 15.25/15.47      inference('simplify', [status(thm)], ['31'])).
% 15.25/15.47  thf('33', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         (((k3_xboole_0 @ X1 @ X0)
% 15.25/15.47            = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 15.25/15.47          | (r2_hidden @ 
% 15.25/15.47             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.25/15.47             X1))),
% 15.25/15.47      inference('sup-', [status(thm)], ['30', '32'])).
% 15.25/15.47  thf('34', plain,
% 15.25/15.47      (![X1 : $i, X2 : $i, X5 : $i]:
% 15.25/15.47         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 15.25/15.47      inference('cnf', [status(esa)], [d4_xboole_0])).
% 15.25/15.47  thf('35', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         (((k3_xboole_0 @ X0 @ X1)
% 15.25/15.47            = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))
% 15.25/15.47          | ~ (r2_hidden @ 
% 15.25/15.47               (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 15.25/15.47               (k3_xboole_0 @ X0 @ X1))
% 15.25/15.47          | ~ (r2_hidden @ 
% 15.25/15.47               (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 15.25/15.47               (k3_xboole_0 @ X0 @ X1))
% 15.25/15.47          | ((k3_xboole_0 @ X0 @ X1)
% 15.25/15.47              = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)))),
% 15.25/15.47      inference('sup-', [status(thm)], ['33', '34'])).
% 15.25/15.47  thf('36', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         (~ (r2_hidden @ 
% 15.25/15.47             (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 15.25/15.47             (k3_xboole_0 @ X0 @ X1))
% 15.25/15.47          | ((k3_xboole_0 @ X0 @ X1)
% 15.25/15.47              = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)))),
% 15.25/15.47      inference('simplify', [status(thm)], ['35'])).
% 15.25/15.47  thf('37', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 15.25/15.47          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 15.25/15.47      inference('eq_fact', [status(thm)], ['29'])).
% 15.25/15.47  thf('38', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         ((k3_xboole_0 @ X0 @ X1)
% 15.25/15.47           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 15.25/15.47      inference('clc', [status(thm)], ['36', '37'])).
% 15.25/15.47  thf('39', plain,
% 15.25/15.47      ((((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))
% 15.25/15.47          = (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B))
% 15.25/15.47        | ((sk_A) = (sk_C)))),
% 15.25/15.47      inference('sup+', [status(thm)], ['28', '38'])).
% 15.25/15.47  thf('40', plain,
% 15.25/15.47      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)
% 15.25/15.47         != (k2_tarski @ sk_A @ sk_C))),
% 15.25/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.25/15.47  thf('41', plain,
% 15.25/15.47      ((((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))
% 15.25/15.47          != (k2_tarski @ sk_A @ sk_C))
% 15.25/15.47        | ((sk_A) = (sk_C)))),
% 15.25/15.47      inference('sup-', [status(thm)], ['39', '40'])).
% 15.25/15.47  thf('42', plain,
% 15.25/15.47      ((((k2_tarski @ sk_A @ sk_C)
% 15.25/15.47          = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))
% 15.25/15.47        | ((sk_A) = (sk_C)))),
% 15.25/15.47      inference('simplify', [status(thm)], ['27'])).
% 15.25/15.47  thf('43', plain, (((sk_A) = (sk_C))),
% 15.25/15.47      inference('clc', [status(thm)], ['41', '42'])).
% 15.25/15.47  thf('44', plain,
% 15.25/15.47      (![X20 : $i, X21 : $i]:
% 15.25/15.47         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 15.25/15.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 15.25/15.47  thf('45', plain,
% 15.25/15.47      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 15.25/15.47         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 15.25/15.47          | (r2_hidden @ X13 @ X17)
% 15.25/15.47          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 15.25/15.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 15.25/15.47  thf('46', plain,
% 15.25/15.47      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 15.25/15.47         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 15.25/15.47          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 15.25/15.47      inference('simplify', [status(thm)], ['45'])).
% 15.25/15.47  thf('47', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 15.25/15.47          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 15.25/15.47      inference('sup+', [status(thm)], ['44', '46'])).
% 15.25/15.47  thf('48', plain,
% 15.25/15.47      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 15.25/15.47         (((X9) != (X8)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 15.25/15.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.25/15.47  thf('49', plain,
% 15.25/15.47      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X8 @ X10 @ X11 @ X8)),
% 15.25/15.47      inference('simplify', [status(thm)], ['48'])).
% 15.25/15.47  thf('50', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 15.25/15.47      inference('sup-', [status(thm)], ['47', '49'])).
% 15.25/15.47  thf('51', plain, ((r2_hidden @ sk_A @ sk_B)),
% 15.25/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.25/15.47  thf('52', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.25/15.47         (~ (r2_hidden @ X0 @ X1)
% 15.25/15.47          | ~ (r2_hidden @ X0 @ X2)
% 15.25/15.47          | (r2_hidden @ X0 @ X3)
% 15.25/15.47          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 15.25/15.47      inference('cnf', [status(esa)], [d4_xboole_0])).
% 15.25/15.47  thf('53', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 15.25/15.47          | ~ (r2_hidden @ X0 @ X2)
% 15.25/15.47          | ~ (r2_hidden @ X0 @ X1))),
% 15.25/15.47      inference('simplify', [status(thm)], ['52'])).
% 15.25/15.47  thf('54', plain,
% 15.25/15.47      (![X0 : $i]:
% 15.25/15.47         (~ (r2_hidden @ sk_A @ X0)
% 15.25/15.47          | (r2_hidden @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))),
% 15.25/15.47      inference('sup-', [status(thm)], ['51', '53'])).
% 15.25/15.47  thf('55', plain,
% 15.25/15.47      (![X0 : $i]:
% 15.25/15.47         (r2_hidden @ sk_A @ (k3_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_B))),
% 15.25/15.47      inference('sup-', [status(thm)], ['50', '54'])).
% 15.25/15.47  thf('56', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         (((k2_tarski @ X0 @ X1) = (k3_xboole_0 @ X2 @ (k2_tarski @ X0 @ X1)))
% 15.25/15.47          | ((sk_D @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X0 @ X1) @ X2) = (X1))
% 15.25/15.47          | ((sk_D @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X0 @ X1) @ X2) = (X0)))),
% 15.25/15.47      inference('simplify', [status(thm)], ['10'])).
% 15.25/15.47  thf('57', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         (((X0) != (X2))
% 15.25/15.47          | ((sk_D @ (k2_tarski @ X2 @ X0) @ (k2_tarski @ X2 @ X0) @ X1) = (X2))
% 15.25/15.47          | ((k2_tarski @ X2 @ X0) = (k3_xboole_0 @ X1 @ (k2_tarski @ X2 @ X0))))),
% 15.25/15.47      inference('eq_fact', [status(thm)], ['56'])).
% 15.25/15.47  thf('58', plain,
% 15.25/15.47      (![X1 : $i, X2 : $i]:
% 15.25/15.47         (((k2_tarski @ X2 @ X2) = (k3_xboole_0 @ X1 @ (k2_tarski @ X2 @ X2)))
% 15.25/15.47          | ((sk_D @ (k2_tarski @ X2 @ X2) @ (k2_tarski @ X2 @ X2) @ X1) = (X2)))),
% 15.25/15.47      inference('simplify', [status(thm)], ['57'])).
% 15.25/15.47  thf('59', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         ((k3_xboole_0 @ X0 @ X1)
% 15.25/15.47           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 15.25/15.47      inference('clc', [status(thm)], ['36', '37'])).
% 15.25/15.47  thf('60', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 15.25/15.47          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 15.25/15.47      inference('eq_fact', [status(thm)], ['3'])).
% 15.25/15.47  thf('61', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 15.25/15.47      inference('clc', [status(thm)], ['15', '16'])).
% 15.25/15.47  thf('62', plain,
% 15.25/15.47      (![X0 : $i]:
% 15.25/15.47         (((X0) = (k3_xboole_0 @ X0 @ X0)) | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 15.25/15.47      inference('sup-', [status(thm)], ['60', '61'])).
% 15.25/15.47  thf('63', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 15.25/15.47      inference('simplify', [status(thm)], ['62'])).
% 15.25/15.47  thf('64', plain,
% 15.25/15.47      (![X1 : $i, X2 : $i, X5 : $i]:
% 15.25/15.47         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 15.25/15.47          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 15.25/15.47          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 15.25/15.47      inference('cnf', [status(esa)], [d4_xboole_0])).
% 15.25/15.47  thf('65', plain,
% 15.25/15.47      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 15.25/15.47         (~ (r2_hidden @ X4 @ X3)
% 15.25/15.47          | (r2_hidden @ X4 @ X2)
% 15.25/15.47          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 15.25/15.47      inference('cnf', [status(esa)], [d4_xboole_0])).
% 15.25/15.47  thf('66', plain,
% 15.25/15.47      (![X1 : $i, X2 : $i, X4 : $i]:
% 15.25/15.47         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 15.25/15.47      inference('simplify', [status(thm)], ['65'])).
% 15.25/15.47  thf('67', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.25/15.47         ((r2_hidden @ (sk_D @ X3 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 15.25/15.47          | ((X3) = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 15.25/15.47          | (r2_hidden @ (sk_D @ X3 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 15.25/15.47      inference('sup-', [status(thm)], ['64', '66'])).
% 15.25/15.47  thf('68', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         ((r2_hidden @ (sk_D @ X0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 15.25/15.47          | ((X0) = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 15.25/15.47      inference('eq_fact', [status(thm)], ['67'])).
% 15.25/15.47  thf('69', plain,
% 15.25/15.47      (![X1 : $i, X2 : $i, X5 : $i]:
% 15.25/15.47         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 15.25/15.47          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 15.25/15.47          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 15.25/15.47      inference('cnf', [status(esa)], [d4_xboole_0])).
% 15.25/15.47  thf('70', plain,
% 15.25/15.47      (![X1 : $i, X2 : $i, X4 : $i]:
% 15.25/15.47         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 15.25/15.47      inference('simplify', [status(thm)], ['65'])).
% 15.25/15.47  thf('71', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.25/15.47         ((r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X3 @ X2) @ X3)
% 15.25/15.47          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X2 @ X3))
% 15.25/15.47          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X3 @ X2) @ X0))),
% 15.25/15.47      inference('sup-', [status(thm)], ['69', '70'])).
% 15.25/15.47  thf('72', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         ((r2_hidden @ (sk_D @ (k3_xboole_0 @ X2 @ X0) @ X0 @ X1) @ X0)
% 15.25/15.47          | ((k3_xboole_0 @ X2 @ X0) = (k3_xboole_0 @ X1 @ X0)))),
% 15.25/15.47      inference('eq_fact', [status(thm)], ['71'])).
% 15.25/15.47  thf('73', plain,
% 15.25/15.47      (![X1 : $i, X2 : $i, X5 : $i]:
% 15.25/15.47         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 15.25/15.47      inference('cnf', [status(esa)], [d4_xboole_0])).
% 15.25/15.47  thf('74', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         (((k3_xboole_0 @ X2 @ X0) = (k3_xboole_0 @ X1 @ X0))
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X2 @ X0) @ X0 @ X1) @ 
% 15.25/15.47               (k3_xboole_0 @ X2 @ X0))
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X2 @ X0) @ X0 @ X1) @ X1)
% 15.25/15.47          | ((k3_xboole_0 @ X2 @ X0) = (k3_xboole_0 @ X1 @ X0)))),
% 15.25/15.47      inference('sup-', [status(thm)], ['72', '73'])).
% 15.25/15.47  thf('75', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         (~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X2 @ X0) @ X0 @ X1) @ X1)
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X2 @ X0) @ X0 @ X1) @ 
% 15.25/15.47               (k3_xboole_0 @ X2 @ X0))
% 15.25/15.47          | ((k3_xboole_0 @ X2 @ X0) = (k3_xboole_0 @ X1 @ X0)))),
% 15.25/15.47      inference('simplify', [status(thm)], ['74'])).
% 15.25/15.47  thf('76', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         (((k3_xboole_0 @ X1 @ X0)
% 15.25/15.47            = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))
% 15.25/15.47          | ((k3_xboole_0 @ X1 @ X0)
% 15.25/15.47              = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.25/15.47                 X0))
% 15.25/15.47          | ~ (r2_hidden @ 
% 15.25/15.47               (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X0 @ 
% 15.25/15.47                (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 15.25/15.47               (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 15.25/15.47      inference('sup-', [status(thm)], ['68', '75'])).
% 15.25/15.47  thf('77', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         (~ (r2_hidden @ 
% 15.25/15.47             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X0 @ 
% 15.25/15.47              (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 15.25/15.47             (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 15.25/15.47          | ((k3_xboole_0 @ X1 @ X0)
% 15.25/15.47              = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.25/15.47                 X0)))),
% 15.25/15.47      inference('simplify', [status(thm)], ['76'])).
% 15.25/15.47  thf('78', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         (~ (r2_hidden @ 
% 15.25/15.47             (sk_D @ X0 @ X0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0))) @ 
% 15.25/15.47             (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0)))
% 15.25/15.47          | ((k3_xboole_0 @ X0 @ X0)
% 15.25/15.47              = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0)) @ 
% 15.25/15.47                 X0)))),
% 15.25/15.47      inference('sup-', [status(thm)], ['63', '77'])).
% 15.25/15.47  thf('79', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 15.25/15.47      inference('simplify', [status(thm)], ['62'])).
% 15.25/15.47  thf('80', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 15.25/15.47      inference('simplify', [status(thm)], ['62'])).
% 15.25/15.47  thf('81', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 15.25/15.47      inference('simplify', [status(thm)], ['62'])).
% 15.25/15.47  thf('82', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 15.25/15.47      inference('simplify', [status(thm)], ['62'])).
% 15.25/15.47  thf('83', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 15.25/15.47          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 15.25/15.47      inference('eq_fact', [status(thm)], ['29'])).
% 15.25/15.47  thf('84', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.25/15.47         (~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X2 @ X0) @ X0 @ X1) @ X1)
% 15.25/15.47          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X2 @ X0) @ X0 @ X1) @ 
% 15.25/15.47               (k3_xboole_0 @ X2 @ X0))
% 15.25/15.47          | ((k3_xboole_0 @ X2 @ X0) = (k3_xboole_0 @ X1 @ X0)))),
% 15.25/15.47      inference('simplify', [status(thm)], ['74'])).
% 15.25/15.47  thf('85', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         (((k3_xboole_0 @ X1 @ X0)
% 15.25/15.47            = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))
% 15.25/15.47          | ((k3_xboole_0 @ X1 @ X0)
% 15.25/15.47              = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))
% 15.25/15.47          | ~ (r2_hidden @ 
% 15.25/15.47               (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.25/15.47               (k3_xboole_0 @ X1 @ X0)))),
% 15.25/15.47      inference('sup-', [status(thm)], ['83', '84'])).
% 15.25/15.47  thf('86', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         (~ (r2_hidden @ 
% 15.25/15.47             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.25/15.47             (k3_xboole_0 @ X1 @ X0))
% 15.25/15.47          | ((k3_xboole_0 @ X1 @ X0)
% 15.25/15.47              = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)))),
% 15.25/15.47      inference('simplify', [status(thm)], ['85'])).
% 15.25/15.47  thf('87', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 15.25/15.47          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 15.25/15.47      inference('eq_fact', [status(thm)], ['29'])).
% 15.25/15.47  thf('88', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         ((k3_xboole_0 @ X1 @ X0)
% 15.25/15.47           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 15.25/15.47      inference('clc', [status(thm)], ['86', '87'])).
% 15.25/15.47  thf('89', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.25/15.47             (k3_xboole_0 @ X1 @ X0))
% 15.25/15.47          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 15.25/15.47      inference('demod', [status(thm)], ['78', '79', '80', '81', '82', '88'])).
% 15.25/15.47  thf('90', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         (~ (r2_hidden @ (sk_D @ X1 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.25/15.47             (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))
% 15.25/15.47          | ((X1) = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 15.25/15.47      inference('sup-', [status(thm)], ['59', '89'])).
% 15.25/15.47  thf('91', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         ((k3_xboole_0 @ X0 @ X1)
% 15.25/15.47           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 15.25/15.47      inference('clc', [status(thm)], ['36', '37'])).
% 15.25/15.47  thf('92', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         ((k3_xboole_0 @ X0 @ X1)
% 15.25/15.47           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 15.25/15.47      inference('clc', [status(thm)], ['36', '37'])).
% 15.25/15.47  thf('93', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         (~ (r2_hidden @ (sk_D @ X1 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.25/15.47             (k3_xboole_0 @ X1 @ X0))
% 15.25/15.47          | ((X1) = (k3_xboole_0 @ X1 @ X0)))),
% 15.25/15.47      inference('demod', [status(thm)], ['90', '91', '92'])).
% 15.25/15.47  thf('94', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1))
% 15.25/15.47          | ((k2_tarski @ X0 @ X0)
% 15.25/15.47              = (k3_xboole_0 @ (k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1) @ 
% 15.25/15.47                 (k2_tarski @ X0 @ X0)))
% 15.25/15.47          | ((k2_tarski @ X0 @ X0) = (k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1)))),
% 15.25/15.47      inference('sup-', [status(thm)], ['58', '93'])).
% 15.25/15.47  thf('95', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         ((k3_xboole_0 @ X0 @ X1)
% 15.25/15.47           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 15.25/15.47      inference('clc', [status(thm)], ['36', '37'])).
% 15.25/15.47  thf('96', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1))
% 15.25/15.47          | ((k2_tarski @ X0 @ X0) = (k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1))
% 15.25/15.47          | ((k2_tarski @ X0 @ X0) = (k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1)))),
% 15.25/15.47      inference('demod', [status(thm)], ['94', '95'])).
% 15.25/15.47  thf('97', plain,
% 15.25/15.47      (![X0 : $i, X1 : $i]:
% 15.25/15.47         (((k2_tarski @ X0 @ X0) = (k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1))
% 15.25/15.47          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1)))),
% 15.25/15.47      inference('simplify', [status(thm)], ['96'])).
% 15.25/15.47  thf('98', plain,
% 15.25/15.47      (((k2_tarski @ sk_A @ sk_A)
% 15.25/15.47         = (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ sk_B))),
% 15.25/15.47      inference('sup-', [status(thm)], ['55', '97'])).
% 15.25/15.47  thf('99', plain, (((sk_A) = (sk_C))),
% 15.25/15.47      inference('clc', [status(thm)], ['41', '42'])).
% 15.25/15.47  thf('100', plain, (((k2_tarski @ sk_A @ sk_A) != (k2_tarski @ sk_A @ sk_A))),
% 15.25/15.47      inference('demod', [status(thm)], ['0', '43', '98', '99'])).
% 15.25/15.47  thf('101', plain, ($false), inference('simplify', [status(thm)], ['100'])).
% 15.25/15.47  
% 15.25/15.47  % SZS output end Refutation
% 15.25/15.47  
% 15.25/15.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

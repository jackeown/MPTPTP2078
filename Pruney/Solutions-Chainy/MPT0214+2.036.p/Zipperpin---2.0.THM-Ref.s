%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oXvvPCrhem

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 167 expanded)
%              Number of leaves         :   23 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :  873 (1458 expanded)
%              Number of equality atoms :   77 ( 136 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ( X10 = X11 )
      | ( X10 = X12 )
      | ( X10 = X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t6_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,
    ( ( r2_hidden @ ( sk_C @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
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

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( zip_tseitin_0 @ X19 @ X15 @ X16 @ X17 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X15 @ X16 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ~ ( zip_tseitin_0 @ ( sk_C @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,
    ( ( ( sk_C @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = sk_A )
    | ( ( sk_C @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = sk_A )
    | ( ( sk_C @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = sk_A )
    | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('14',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( ( sk_C @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = sk_A ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
    | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
    | ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('23',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ( X10 = X11 )
      | ( X10 = X12 )
      | ( X10 = X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('26',plain,(
    ! [X49: $i,X50: $i] :
      ( ( X50
        = ( k1_tarski @ X49 ) )
      | ( X50 = k1_xboole_0 )
      | ~ ( r1_tarski @ X50 @ ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_B )
      | ( X0 = sk_B )
      | ( X0 = sk_B )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,
    ( ( sk_A = sk_B )
    | ( k1_xboole_0
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('35',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X14 @ X18 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X9 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ( X10 = X11 )
      | ( X10 = X12 )
      | ( X10 = X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_tarski @ X50 @ ( k1_tarski @ X51 ) )
      | ( X50
       != ( k1_tarski @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('45',plain,(
    ! [X51: $i] :
      ( r1_tarski @ ( k1_tarski @ X51 ) @ ( k1_tarski @ X51 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('58',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('59',plain,(
    ! [X51: $i] :
      ( r1_tarski @ ( k1_tarski @ X51 ) @ ( k1_tarski @ X51 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','66'])).

thf('68',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['35','67'])).

thf('69',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_tarski @ X50 @ ( k1_tarski @ X51 ) )
      | ( X50 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('70',plain,(
    ! [X51: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X51 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('76',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','78'])).

thf('80',plain,(
    $false ),
    inference('sup-',[status(thm)],['68','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oXvvPCrhem
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:10:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 304 iterations in 0.082s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(d1_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.54       ( ![E:$i]:
% 0.20/0.54         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.54           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, axiom,
% 0.20/0.54    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.54     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.54       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.54         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.20/0.54          | ((X10) = (X11))
% 0.20/0.54          | ((X10) = (X12))
% 0.20/0.54          | ((X10) = (X13)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t6_zfmisc_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.20/0.54       ( ( A ) = ( B ) ) ))).
% 0.20/0.54  thf(zf_stmt_1, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i]:
% 0.20/0.54        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.20/0.54          ( ( A ) = ( B ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.20/0.54  thf('1', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.54  thf(t28_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.54         = (k1_tarski @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.54  thf(t4_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.54            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         ((r1_xboole_0 @ X3 @ X4)
% 0.20/0.54          | (r2_hidden @ (sk_C @ X4 @ X3) @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (((r2_hidden @ (sk_C @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 0.20/0.54         (k1_tarski @ sk_A))
% 0.20/0.54        | (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.54  thf(t69_enumset1, axiom,
% 0.20/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.54  thf('6', plain, (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.20/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.54  thf(t70_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X22 : $i, X23 : $i]:
% 0.20/0.54         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.20/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.54  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_3, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.54       ( ![E:$i]:
% 0.20/0.54         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X19 @ X18)
% 0.20/0.54          | ~ (zip_tseitin_0 @ X19 @ X15 @ X16 @ X17)
% 0.20/0.54          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 0.20/0.54         (~ (zip_tseitin_0 @ X19 @ X15 @ X16 @ X17)
% 0.20/0.54          | ~ (r2_hidden @ X19 @ (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.54          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.54          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.54        | ~ (zip_tseitin_0 @ 
% 0.20/0.54             (sk_C @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ sk_A @ sk_A @ 
% 0.20/0.54             sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['5', '11'])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      ((((sk_C @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (sk_A))
% 0.20/0.54        | ((sk_C @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (sk_A))
% 0.20/0.54        | ((sk_C @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (sk_A))
% 0.20/0.54        | (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['0', '12'])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.54        | ((sk_C @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (sk_A)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         ((r1_xboole_0 @ X3 @ X4)
% 0.20/0.54          | (r2_hidden @ (sk_C @ X4 @ X3) @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ 
% 0.20/0.54         (k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.20/0.54        | (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.54        | (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.54         = (k1_tarski @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.20/0.54        | (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.54        | (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.54        | (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.54  thf(d7_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.54       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.20/0.54        | ((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.54            = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.54         = (k1_tarski @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      ((((k1_xboole_0) = (k1_tarski @ sk_A))
% 0.20/0.54        | (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.54         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.20/0.54          | ((X10) = (X11))
% 0.20/0.54          | ((X10) = (X12))
% 0.20/0.54          | ((X10) = (X13)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('25', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.54  thf(l3_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X49 : $i, X50 : $i]:
% 0.20/0.54         (((X50) = (k1_tarski @ X49))
% 0.20/0.54          | ((X50) = (k1_xboole_0))
% 0.20/0.54          | ~ (r1_tarski @ X50 @ (k1_tarski @ X49)))),
% 0.20/0.54      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.54          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '10'])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.20/0.54          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.54          | ~ (zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((X0) = (sk_B))
% 0.20/0.54          | ((X0) = (sk_B))
% 0.20/0.54          | ((X0) = (sk_B))
% 0.20/0.54          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.54          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['24', '29'])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.20/0.54          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.54          | ((X0) = (sk_B)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      ((((k1_xboole_0) = (k1_tarski @ sk_A))
% 0.20/0.54        | ((sk_A) = (sk_B))
% 0.20/0.54        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['23', '31'])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      ((((sk_A) = (sk_B)) | ((k1_xboole_0) = (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.54  thf('34', plain, (((sk_A) != (sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.54  thf('35', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (![X22 : $i, X23 : $i]:
% 0.20/0.54         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.20/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.54         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 0.20/0.54          | (r2_hidden @ X14 @ X18)
% 0.20/0.54          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.54         ((r2_hidden @ X14 @ (k1_enumset1 @ X17 @ X16 @ X15))
% 0.20/0.54          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 0.20/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.54          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['36', '38'])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.54         (((X10) != (X9)) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (![X9 : $i, X11 : $i, X12 : $i]: ~ (zip_tseitin_0 @ X9 @ X11 @ X12 @ X9)),
% 0.20/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['39', '41'])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.54         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.20/0.54          | ((X10) = (X11))
% 0.20/0.54          | ((X10) = (X12))
% 0.20/0.54          | ((X10) = (X13)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      (![X50 : $i, X51 : $i]:
% 0.20/0.54         ((r1_tarski @ X50 @ (k1_tarski @ X51)) | ((X50) != (k1_tarski @ X51)))),
% 0.20/0.54      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      (![X51 : $i]: (r1_tarski @ (k1_tarski @ X51) @ (k1_tarski @ X51))),
% 0.20/0.54      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.54           = (k1_tarski @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         ((r1_xboole_0 @ X3 @ X4)
% 0.20/0.54          | (r2_hidden @ (sk_C @ X4 @ X3) @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_C @ (k1_tarski @ X0) @ (k1_tarski @ X0)) @ 
% 0.20/0.54           (k1_tarski @ X0))
% 0.20/0.54          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['47', '48'])).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.54          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '10'])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.54          | ~ (zip_tseitin_0 @ (sk_C @ (k1_tarski @ X0) @ (k1_tarski @ X0)) @ 
% 0.20/0.54               X0 @ X0 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((sk_C @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (X0))
% 0.20/0.54          | ((sk_C @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (X0))
% 0.20/0.54          | ((sk_C @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (X0))
% 0.20/0.54          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['43', '51'])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.54          | ((sk_C @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_C @ (k1_tarski @ X0) @ (k1_tarski @ X0)) @ 
% 0.20/0.54           (k1_tarski @ X0))
% 0.20/0.54          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['47', '48'])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.20/0.54          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.54          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf('56', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.54          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.20/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.20/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      (![X51 : $i]: (r1_tarski @ (k1_tarski @ X51) @ (k1_tarski @ X51))),
% 0.20/0.54      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.54  thf('60', plain,
% 0.20/0.54      (![X0 : $i]: (r1_tarski @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['58', '59'])).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 0.20/0.54           = (k2_tarski @ X0 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.54  thf('63', plain,
% 0.20/0.54      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.20/0.54          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.54  thf('64', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 0.20/0.54          | ~ (r1_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.54  thf('65', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.54          | ~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['57', '64'])).
% 0.20/0.54  thf('66', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.20/0.54          | ~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['56', '65'])).
% 0.20/0.54  thf('67', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['42', '66'])).
% 0.20/0.54  thf('68', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.20/0.54      inference('sup+', [status(thm)], ['35', '67'])).
% 0.20/0.54  thf('69', plain,
% 0.20/0.54      (![X50 : $i, X51 : $i]:
% 0.20/0.54         ((r1_tarski @ X50 @ (k1_tarski @ X51)) | ((X50) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.54  thf('70', plain,
% 0.20/0.54      (![X51 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X51))),
% 0.20/0.54      inference('simplify', [status(thm)], ['69'])).
% 0.20/0.54  thf('71', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.54  thf('72', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.54  thf('73', plain,
% 0.20/0.54      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.20/0.54          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.54  thf('74', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.20/0.54          | ~ (r1_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.54  thf('75', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.54  thf('76', plain,
% 0.20/0.54      (![X0 : $i, X2 : $i]:
% 0.20/0.54         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.54  thf('77', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54          | (r1_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.54  thf('78', plain,
% 0.20/0.54      (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['77'])).
% 0.20/0.54  thf('79', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.54      inference('demod', [status(thm)], ['74', '78'])).
% 0.20/0.54  thf('80', plain, ($false), inference('sup-', [status(thm)], ['68', '79'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

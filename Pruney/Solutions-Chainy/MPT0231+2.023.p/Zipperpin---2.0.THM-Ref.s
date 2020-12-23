%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lr2rHcV34e

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:31 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 265 expanded)
%              Number of leaves         :   24 (  87 expanded)
%              Depth                    :   28
%              Number of atoms          :  810 (2510 expanded)
%              Number of equality atoms :  120 ( 318 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( X7 = X8 )
      | ( X7 = X9 )
      | ( X7 = X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( A = C ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t26_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X47
        = ( k1_tarski @ X46 ) )
      | ( X47 = k1_xboole_0 )
      | ~ ( r1_tarski @ X47 @ ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('3',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B_1 )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( X7 = X8 )
      | ( X7 = X9 )
      | ( X7 = X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( X7 = X8 )
      | ( X7 = X9 )
      | ( X7 = X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( X7 = X8 )
      | ( X7 = X9 )
      | ( X7 = X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B_1 )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
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

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) )
      | ( ( k2_tarski @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ sk_B_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( X0 = sk_B_1 )
      | ( ( k2_tarski @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) )
      | ( ( k2_tarski @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ( X0 = sk_B_1 )
      | ( X0 = sk_A ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( ( k1_tarski @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_C_1 ) )
      = sk_A )
    | ( ( sk_B @ ( k1_tarski @ sk_C_1 ) )
      = sk_B_1 )
    | ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('18',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_C_1 ) )
    | ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_C_1 ) )
      = sk_A )
    | ( ( k1_tarski @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k1_tarski @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_C_1 ) )
      = sk_A )
    | ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_C_1 ) )
      = sk_A )
    | ( ( k1_tarski @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_B_1 = sk_C_1 )
    | ( sk_B_1 = sk_C_1 )
    | ( sk_B_1 = sk_C_1 )
    | ( ( k1_tarski @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_C_1 ) )
      = sk_A )
    | ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','23'])).

thf('25',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_C_1 ) )
      = sk_A )
    | ( ( k1_tarski @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = sk_C_1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( zip_tseitin_0 @ sk_A @ sk_C_1 @ sk_C_1 @ sk_C_1 )
    | ( sk_B_1 = sk_C_1 )
    | ( ( k1_tarski @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = sk_C_1 )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_C_1 )
    | ( sk_A = sk_C_1 )
    | ( sk_B_1 = sk_C_1 )
    | ( ( k1_tarski @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','30'])).

thf('32',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = sk_C_1 )
    | ( sk_A = sk_C_1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B_1 )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_C_1 )
     != k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['35'])).

thf('37',plain,
    ( ( sk_B_1 = sk_C_1 )
    | ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('39',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( r2_hidden @ X11 @ X15 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ~ ( zip_tseitin_0 @ X6 @ X8 @ X9 @ X6 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
    | ( sk_B_1 = sk_C_1 ) ),
    inference('sup+',[status(thm)],['37','44'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('46',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('47',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('54',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    sk_B_1 = sk_C_1 ),
    inference(clc,[status(thm)],['45','54'])).

thf('56',plain,(
    sk_B_1 = sk_C_1 ),
    inference(clc,[status(thm)],['45','54'])).

thf('57',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['3','55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('59',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
    | ( ( k2_tarski @ sk_A @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('61',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_C_1 )
    | ( sk_A = sk_C_1 )
    | ( ( k2_tarski @ sk_A @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','61'])).

thf('63',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_A = sk_C_1 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('65',plain,
    ( ( k2_tarski @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('67',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('69',plain,(
    $false ),
    inference('sup-',[status(thm)],['67','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lr2rHcV34e
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:49:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 251 iterations in 0.128s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.40/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.40/0.59  thf(d1_enumset1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.40/0.59       ( ![E:$i]:
% 0.40/0.59         ( ( r2_hidden @ E @ D ) <=>
% 0.40/0.59           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, axiom,
% 0.40/0.59    (![E:$i,C:$i,B:$i,A:$i]:
% 0.40/0.59     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.40/0.59       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.40/0.59  thf('0', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.59         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.40/0.59          | ((X7) = (X8))
% 0.40/0.59          | ((X7) = (X9))
% 0.40/0.59          | ((X7) = (X10)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t26_zfmisc_1, conjecture,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.40/0.59       ( ( A ) = ( C ) ) ))).
% 0.40/0.59  thf(zf_stmt_1, negated_conjecture,
% 0.40/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.59        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.40/0.59          ( ( A ) = ( C ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t26_zfmisc_1])).
% 0.40/0.59  thf('1', plain,
% 0.40/0.59      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ (k1_tarski @ sk_C_1))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.59  thf(l3_zfmisc_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.40/0.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      (![X46 : $i, X47 : $i]:
% 0.40/0.59         (((X47) = (k1_tarski @ X46))
% 0.40/0.59          | ((X47) = (k1_xboole_0))
% 0.40/0.59          | ~ (r1_tarski @ X47 @ (k1_tarski @ X46)))),
% 0.40/0.59      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.40/0.59  thf('3', plain,
% 0.40/0.59      ((((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.40/0.59        | ((k2_tarski @ sk_A @ sk_B_1) = (k1_tarski @ sk_C_1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.59         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.40/0.59          | ((X7) = (X8))
% 0.40/0.59          | ((X7) = (X9))
% 0.40/0.59          | ((X7) = (X10)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.59         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.40/0.59          | ((X7) = (X8))
% 0.40/0.59          | ((X7) = (X9))
% 0.40/0.59          | ((X7) = (X10)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t7_xboole_0, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.40/0.59          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.40/0.59  thf('6', plain,
% 0.40/0.59      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.59         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.40/0.59          | ((X7) = (X8))
% 0.40/0.59          | ((X7) = (X9))
% 0.40/0.59          | ((X7) = (X10)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      ((((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.40/0.59        | ((k2_tarski @ sk_A @ sk_B_1) = (k1_tarski @ sk_C_1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.59  thf(t70_enumset1, axiom,
% 0.40/0.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.40/0.59  thf('9', plain,
% 0.40/0.59      (![X19 : $i, X20 : $i]:
% 0.40/0.59         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.40/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.59  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.40/0.59  thf(zf_stmt_3, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.40/0.59       ( ![E:$i]:
% 0.40/0.59         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.40/0.59  thf('10', plain,
% 0.40/0.59      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X16 @ X15)
% 0.40/0.59          | ~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.40/0.59          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.40/0.59         (~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.40/0.59          | ~ (r2_hidden @ X16 @ (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['10'])).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.40/0.59          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['9', '11'])).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_C_1))
% 0.40/0.59          | ((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.40/0.59          | ~ (zip_tseitin_0 @ X0 @ sk_B_1 @ sk_A @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['8', '12'])).
% 0.40/0.59  thf('14', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((X0) = (sk_A))
% 0.40/0.59          | ((X0) = (sk_A))
% 0.40/0.59          | ((X0) = (sk_B_1))
% 0.40/0.59          | ((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.40/0.59          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_C_1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['7', '13'])).
% 0.40/0.59  thf('15', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_C_1))
% 0.40/0.59          | ((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.40/0.59          | ((X0) = (sk_B_1))
% 0.40/0.59          | ((X0) = (sk_A)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['14'])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      ((((k1_tarski @ sk_C_1) = (k1_xboole_0))
% 0.40/0.59        | ((sk_B @ (k1_tarski @ sk_C_1)) = (sk_A))
% 0.40/0.59        | ((sk_B @ (k1_tarski @ sk_C_1)) = (sk_B_1))
% 0.40/0.59        | ((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['6', '15'])).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.40/0.59  thf('18', plain,
% 0.40/0.59      (((r2_hidden @ sk_B_1 @ (k1_tarski @ sk_C_1))
% 0.40/0.59        | ((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.40/0.59        | ((sk_B @ (k1_tarski @ sk_C_1)) = (sk_A))
% 0.40/0.59        | ((k1_tarski @ sk_C_1) = (k1_xboole_0))
% 0.40/0.59        | ((k1_tarski @ sk_C_1) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      ((((k1_tarski @ sk_C_1) = (k1_xboole_0))
% 0.40/0.59        | ((sk_B @ (k1_tarski @ sk_C_1)) = (sk_A))
% 0.40/0.59        | ((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.40/0.59        | (r2_hidden @ sk_B_1 @ (k1_tarski @ sk_C_1)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['18'])).
% 0.40/0.59  thf(t69_enumset1, axiom,
% 0.40/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.40/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.40/0.59          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['9', '11'])).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.40/0.59          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.59  thf('23', plain,
% 0.40/0.59      ((((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.40/0.59        | ((sk_B @ (k1_tarski @ sk_C_1)) = (sk_A))
% 0.40/0.59        | ((k1_tarski @ sk_C_1) = (k1_xboole_0))
% 0.40/0.59        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['19', '22'])).
% 0.40/0.59  thf('24', plain,
% 0.40/0.59      ((((sk_B_1) = (sk_C_1))
% 0.40/0.59        | ((sk_B_1) = (sk_C_1))
% 0.40/0.59        | ((sk_B_1) = (sk_C_1))
% 0.40/0.59        | ((k1_tarski @ sk_C_1) = (k1_xboole_0))
% 0.40/0.59        | ((sk_B @ (k1_tarski @ sk_C_1)) = (sk_A))
% 0.40/0.59        | ((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['5', '23'])).
% 0.40/0.59  thf('25', plain,
% 0.40/0.59      ((((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.40/0.59        | ((sk_B @ (k1_tarski @ sk_C_1)) = (sk_A))
% 0.40/0.59        | ((k1_tarski @ sk_C_1) = (k1_xboole_0))
% 0.40/0.59        | ((sk_B_1) = (sk_C_1)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['24'])).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.40/0.59  thf('27', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.40/0.59          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.40/0.59          | ~ (zip_tseitin_0 @ (sk_B @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      ((~ (zip_tseitin_0 @ sk_A @ sk_C_1 @ sk_C_1 @ sk_C_1)
% 0.40/0.59        | ((sk_B_1) = (sk_C_1))
% 0.40/0.59        | ((k1_tarski @ sk_C_1) = (k1_xboole_0))
% 0.40/0.59        | ((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.40/0.59        | ((k1_tarski @ sk_C_1) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['25', '28'])).
% 0.40/0.59  thf('30', plain,
% 0.40/0.59      ((((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.40/0.59        | ((k1_tarski @ sk_C_1) = (k1_xboole_0))
% 0.40/0.59        | ((sk_B_1) = (sk_C_1))
% 0.40/0.59        | ~ (zip_tseitin_0 @ sk_A @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.40/0.59      inference('simplify', [status(thm)], ['29'])).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      ((((sk_A) = (sk_C_1))
% 0.40/0.59        | ((sk_A) = (sk_C_1))
% 0.40/0.59        | ((sk_A) = (sk_C_1))
% 0.40/0.59        | ((sk_B_1) = (sk_C_1))
% 0.40/0.59        | ((k1_tarski @ sk_C_1) = (k1_xboole_0))
% 0.40/0.59        | ((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['4', '30'])).
% 0.40/0.59  thf('32', plain,
% 0.40/0.59      ((((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.40/0.59        | ((k1_tarski @ sk_C_1) = (k1_xboole_0))
% 0.40/0.59        | ((sk_B_1) = (sk_C_1))
% 0.40/0.59        | ((sk_A) = (sk_C_1)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['31'])).
% 0.40/0.59  thf('33', plain, (((sk_A) != (sk_C_1))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.59  thf('34', plain,
% 0.40/0.59      ((((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.40/0.59        | ((k1_tarski @ sk_C_1) = (k1_xboole_0))
% 0.40/0.59        | ((sk_B_1) = (sk_C_1)))),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.40/0.59  thf('35', plain,
% 0.40/0.59      ((((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.40/0.59        | ((k2_tarski @ sk_A @ sk_B_1) = (k1_tarski @ sk_C_1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.59  thf('36', plain,
% 0.40/0.59      ((((k1_tarski @ sk_C_1) != (k1_xboole_0))
% 0.40/0.59        | ((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.40/0.59      inference('eq_fact', [status(thm)], ['35'])).
% 0.40/0.59  thf('37', plain,
% 0.40/0.59      ((((sk_B_1) = (sk_C_1)) | ((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.40/0.59      inference('clc', [status(thm)], ['34', '36'])).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      (![X19 : $i, X20 : $i]:
% 0.40/0.59         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.40/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.59  thf('39', plain,
% 0.40/0.59      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.59         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 0.40/0.59          | (r2_hidden @ X11 @ X15)
% 0.40/0.59          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.59  thf('40', plain,
% 0.40/0.59      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.59         ((r2_hidden @ X11 @ (k1_enumset1 @ X14 @ X13 @ X12))
% 0.40/0.59          | (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14))),
% 0.40/0.59      inference('simplify', [status(thm)], ['39'])).
% 0.40/0.59  thf('41', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.40/0.59          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.40/0.59      inference('sup+', [status(thm)], ['38', '40'])).
% 0.40/0.59  thf('42', plain,
% 0.40/0.59      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.40/0.59         (((X7) != (X6)) | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('43', plain,
% 0.40/0.59      (![X6 : $i, X8 : $i, X9 : $i]: ~ (zip_tseitin_0 @ X6 @ X8 @ X9 @ X6)),
% 0.40/0.59      inference('simplify', [status(thm)], ['42'])).
% 0.40/0.59  thf('44', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['41', '43'])).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      (((r2_hidden @ sk_A @ k1_xboole_0) | ((sk_B_1) = (sk_C_1)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['37', '44'])).
% 0.40/0.59  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.40/0.59  thf('46', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.40/0.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.40/0.59  thf('47', plain,
% 0.40/0.59      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.40/0.59  thf(t4_xboole_0, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.59            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.40/0.59  thf('48', plain,
% 0.40/0.59      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.40/0.59          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.40/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.59  thf('49', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.40/0.59  thf('50', plain,
% 0.40/0.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['46', '49'])).
% 0.40/0.59  thf('51', plain,
% 0.40/0.59      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.40/0.59          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.40/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.59  thf('52', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.59  thf('53', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.40/0.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.40/0.59  thf('54', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.40/0.59      inference('demod', [status(thm)], ['52', '53'])).
% 0.40/0.59  thf('55', plain, (((sk_B_1) = (sk_C_1))),
% 0.40/0.59      inference('clc', [status(thm)], ['45', '54'])).
% 0.40/0.59  thf('56', plain, (((sk_B_1) = (sk_C_1))),
% 0.40/0.59      inference('clc', [status(thm)], ['45', '54'])).
% 0.40/0.59  thf('57', plain,
% 0.40/0.59      ((((k2_tarski @ sk_A @ sk_C_1) = (k1_xboole_0))
% 0.40/0.59        | ((k2_tarski @ sk_A @ sk_C_1) = (k1_tarski @ sk_C_1)))),
% 0.40/0.59      inference('demod', [status(thm)], ['3', '55', '56'])).
% 0.40/0.59  thf('58', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['41', '43'])).
% 0.40/0.59  thf('59', plain,
% 0.40/0.59      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_1))
% 0.40/0.59        | ((k2_tarski @ sk_A @ sk_C_1) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['57', '58'])).
% 0.40/0.59  thf('60', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.40/0.59          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.59  thf('61', plain,
% 0.40/0.59      ((((k2_tarski @ sk_A @ sk_C_1) = (k1_xboole_0))
% 0.40/0.59        | ~ (zip_tseitin_0 @ sk_A @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['59', '60'])).
% 0.40/0.59  thf('62', plain,
% 0.40/0.59      ((((sk_A) = (sk_C_1))
% 0.40/0.59        | ((sk_A) = (sk_C_1))
% 0.40/0.59        | ((sk_A) = (sk_C_1))
% 0.40/0.59        | ((k2_tarski @ sk_A @ sk_C_1) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['0', '61'])).
% 0.40/0.59  thf('63', plain,
% 0.40/0.59      ((((k2_tarski @ sk_A @ sk_C_1) = (k1_xboole_0)) | ((sk_A) = (sk_C_1)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['62'])).
% 0.40/0.59  thf('64', plain, (((sk_A) != (sk_C_1))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.59  thf('65', plain, (((k2_tarski @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.40/0.59  thf('66', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['41', '43'])).
% 0.40/0.59  thf('67', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.40/0.59      inference('sup+', [status(thm)], ['65', '66'])).
% 0.40/0.59  thf('68', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.40/0.59      inference('demod', [status(thm)], ['52', '53'])).
% 0.40/0.59  thf('69', plain, ($false), inference('sup-', [status(thm)], ['67', '68'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.40/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

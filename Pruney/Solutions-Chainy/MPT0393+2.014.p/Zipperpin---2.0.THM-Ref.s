%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pea3WwHGuP

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:42 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 302 expanded)
%              Number of leaves         :   26 (  97 expanded)
%              Depth                    :   16
%              Number of atoms          :  665 (2489 expanded)
%              Number of equality atoms :   69 ( 259 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
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

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( r2_hidden @ X12 @ X16 )
      | ( X16
       != ( k1_enumset1 @ X15 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ ( k1_enumset1 @ X15 @ X14 @ X13 ) )
      | ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t5_setfam_1,axiom,(
    ! [A: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ A )
     => ( ( k1_setfam_1 @ A )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X46: $i] :
      ( ( ( k1_setfam_1 @ X46 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t5_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 @ X1 @ X2 )
      | ( ( k1_setfam_1 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ k1_xboole_0 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X9 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ~ ( zip_tseitin_0 @ X9 @ X9 @ X10 @ X7 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ ( k1_enumset1 @ X15 @ X14 @ X13 ) )
      | ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X7 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ~ ( zip_tseitin_0 @ X7 @ X9 @ X10 @ X7 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('15',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X44 ) @ X45 )
      | ~ ( r2_hidden @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['8','16'])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X48 @ X47 ) @ X47 )
      | ( r1_tarski @ X48 @ ( k1_setfam_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('19',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X36 ) @ ( k1_tarski @ X37 ) )
        = ( k1_tarski @ X36 ) )
      | ( X36 = X37 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('20',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38 != X40 )
      | ~ ( r2_hidden @ X38 @ ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('21',plain,(
    ! [X39: $i,X40: $i] :
      ~ ( r2_hidden @ X40 @ ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('26',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ ( k1_tarski @ X32 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X44 ) @ X45 )
      | ~ ( r2_hidden @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_C_2 @ X0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( r1_tarski @ X48 @ ( sk_C_2 @ X48 @ X47 ) )
      | ( r1_tarski @ X48 @ ( k1_setfam_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('40',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('43',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( r2_hidden @ X38 @ X39 )
      | ~ ( r2_hidden @ X38 @ ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','53'])).

thf('55',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf('56',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X36 != X35 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X36 ) @ ( k1_tarski @ X35 ) )
       != ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('57',plain,(
    ! [X35: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X35 ) @ ( k1_tarski @ X35 ) )
     != ( k1_tarski @ X35 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf('60',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf('61',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pea3WwHGuP
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:00:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.29/1.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.29/1.47  % Solved by: fo/fo7.sh
% 1.29/1.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.29/1.47  % done 1248 iterations in 1.019s
% 1.29/1.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.29/1.47  % SZS output start Refutation
% 1.29/1.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.29/1.47  thf(sk_A_type, type, sk_A: $i).
% 1.29/1.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.29/1.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.29/1.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.29/1.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.29/1.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.29/1.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.29/1.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.29/1.47  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.29/1.47  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 1.29/1.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.29/1.47  thf(t70_enumset1, axiom,
% 1.29/1.47    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.29/1.47  thf('0', plain,
% 1.29/1.47      (![X20 : $i, X21 : $i]:
% 1.29/1.47         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 1.29/1.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.29/1.47  thf(d1_enumset1, axiom,
% 1.29/1.47    (![A:$i,B:$i,C:$i,D:$i]:
% 1.29/1.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.29/1.47       ( ![E:$i]:
% 1.29/1.47         ( ( r2_hidden @ E @ D ) <=>
% 1.29/1.47           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.29/1.47  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.29/1.47  thf(zf_stmt_1, axiom,
% 1.29/1.47    (![E:$i,C:$i,B:$i,A:$i]:
% 1.29/1.47     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.29/1.47       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.29/1.47  thf(zf_stmt_2, axiom,
% 1.29/1.47    (![A:$i,B:$i,C:$i,D:$i]:
% 1.29/1.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.29/1.47       ( ![E:$i]:
% 1.29/1.47         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.29/1.47  thf('1', plain,
% 1.29/1.47      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.29/1.47         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 1.29/1.47          | (r2_hidden @ X12 @ X16)
% 1.29/1.47          | ((X16) != (k1_enumset1 @ X15 @ X14 @ X13)))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.29/1.47  thf('2', plain,
% 1.29/1.47      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.29/1.47         ((r2_hidden @ X12 @ (k1_enumset1 @ X15 @ X14 @ X13))
% 1.29/1.47          | (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 1.29/1.47      inference('simplify', [status(thm)], ['1'])).
% 1.29/1.47  thf(t5_setfam_1, axiom,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 1.29/1.47       ( ( k1_setfam_1 @ A ) = ( k1_xboole_0 ) ) ))).
% 1.29/1.47  thf('3', plain,
% 1.29/1.47      (![X46 : $i]:
% 1.29/1.47         (((k1_setfam_1 @ X46) = (k1_xboole_0))
% 1.29/1.47          | ~ (r2_hidden @ k1_xboole_0 @ X46))),
% 1.29/1.47      inference('cnf', [status(esa)], [t5_setfam_1])).
% 1.29/1.47  thf('4', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.47         ((zip_tseitin_0 @ k1_xboole_0 @ X0 @ X1 @ X2)
% 1.29/1.47          | ((k1_setfam_1 @ (k1_enumset1 @ X2 @ X1 @ X0)) = (k1_xboole_0)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['2', '3'])).
% 1.29/1.47  thf('5', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k1_xboole_0))
% 1.29/1.47          | (zip_tseitin_0 @ k1_xboole_0 @ X0 @ X1 @ X1))),
% 1.29/1.47      inference('sup+', [status(thm)], ['0', '4'])).
% 1.29/1.47  thf('6', plain,
% 1.29/1.47      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.29/1.47         (((X8) != (X9)) | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X7))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.29/1.47  thf('7', plain,
% 1.29/1.47      (![X7 : $i, X9 : $i, X10 : $i]: ~ (zip_tseitin_0 @ X9 @ X9 @ X10 @ X7)),
% 1.29/1.47      inference('simplify', [status(thm)], ['6'])).
% 1.29/1.47  thf('8', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         ((k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.29/1.47      inference('sup-', [status(thm)], ['5', '7'])).
% 1.29/1.47  thf('9', plain,
% 1.29/1.47      (![X20 : $i, X21 : $i]:
% 1.29/1.47         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 1.29/1.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.29/1.47  thf('10', plain,
% 1.29/1.47      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.29/1.47         ((r2_hidden @ X12 @ (k1_enumset1 @ X15 @ X14 @ X13))
% 1.29/1.47          | (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 1.29/1.47      inference('simplify', [status(thm)], ['1'])).
% 1.29/1.47  thf('11', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.47         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.29/1.47          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.29/1.47      inference('sup+', [status(thm)], ['9', '10'])).
% 1.29/1.47  thf('12', plain,
% 1.29/1.47      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.29/1.47         (((X8) != (X7)) | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X7))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.29/1.47  thf('13', plain,
% 1.29/1.47      (![X7 : $i, X9 : $i, X10 : $i]: ~ (zip_tseitin_0 @ X7 @ X9 @ X10 @ X7)),
% 1.29/1.47      inference('simplify', [status(thm)], ['12'])).
% 1.29/1.47  thf('14', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.29/1.47      inference('sup-', [status(thm)], ['11', '13'])).
% 1.29/1.47  thf(t4_setfam_1, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 1.29/1.47  thf('15', plain,
% 1.29/1.47      (![X44 : $i, X45 : $i]:
% 1.29/1.47         ((r1_tarski @ (k1_setfam_1 @ X44) @ X45) | ~ (r2_hidden @ X45 @ X44))),
% 1.29/1.47      inference('cnf', [status(esa)], [t4_setfam_1])).
% 1.29/1.47  thf('16', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X1)),
% 1.29/1.47      inference('sup-', [status(thm)], ['14', '15'])).
% 1.29/1.47  thf('17', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.29/1.47      inference('sup+', [status(thm)], ['8', '16'])).
% 1.29/1.47  thf(t6_setfam_1, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 1.29/1.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 1.29/1.47  thf('18', plain,
% 1.29/1.47      (![X47 : $i, X48 : $i]:
% 1.29/1.47         (((X47) = (k1_xboole_0))
% 1.29/1.47          | (r2_hidden @ (sk_C_2 @ X48 @ X47) @ X47)
% 1.29/1.47          | (r1_tarski @ X48 @ (k1_setfam_1 @ X47)))),
% 1.29/1.47      inference('cnf', [status(esa)], [t6_setfam_1])).
% 1.29/1.47  thf(t20_zfmisc_1, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.29/1.47         ( k1_tarski @ A ) ) <=>
% 1.29/1.47       ( ( A ) != ( B ) ) ))).
% 1.29/1.47  thf('19', plain,
% 1.29/1.47      (![X36 : $i, X37 : $i]:
% 1.29/1.47         (((k4_xboole_0 @ (k1_tarski @ X36) @ (k1_tarski @ X37))
% 1.29/1.47            = (k1_tarski @ X36))
% 1.29/1.47          | ((X36) = (X37)))),
% 1.29/1.47      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 1.29/1.47  thf(t64_zfmisc_1, axiom,
% 1.29/1.47    (![A:$i,B:$i,C:$i]:
% 1.29/1.47     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 1.29/1.47       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 1.29/1.47  thf('20', plain,
% 1.29/1.47      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.29/1.47         (((X38) != (X40))
% 1.29/1.47          | ~ (r2_hidden @ X38 @ (k4_xboole_0 @ X39 @ (k1_tarski @ X40))))),
% 1.29/1.47      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 1.29/1.47  thf('21', plain,
% 1.29/1.47      (![X39 : $i, X40 : $i]:
% 1.29/1.47         ~ (r2_hidden @ X40 @ (k4_xboole_0 @ X39 @ (k1_tarski @ X40)))),
% 1.29/1.47      inference('simplify', [status(thm)], ['20'])).
% 1.29/1.47  thf('22', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['19', '21'])).
% 1.29/1.47  thf('23', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.29/1.47          | ((k1_tarski @ X0) = (k1_xboole_0))
% 1.29/1.47          | ((X0) = (sk_C_2 @ X1 @ (k1_tarski @ X0))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['18', '22'])).
% 1.29/1.47  thf(d10_xboole_0, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.29/1.47  thf('24', plain,
% 1.29/1.47      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.29/1.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.29/1.47  thf('25', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.29/1.47      inference('simplify', [status(thm)], ['24'])).
% 1.29/1.47  thf(l1_zfmisc_1, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.29/1.47  thf('26', plain,
% 1.29/1.47      (![X32 : $i, X33 : $i]:
% 1.29/1.47         ((r2_hidden @ X32 @ X33) | ~ (r1_tarski @ (k1_tarski @ X32) @ X33))),
% 1.29/1.47      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.29/1.47  thf('27', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.29/1.47      inference('sup-', [status(thm)], ['25', '26'])).
% 1.29/1.47  thf('28', plain,
% 1.29/1.47      (![X44 : $i, X45 : $i]:
% 1.29/1.47         ((r1_tarski @ (k1_setfam_1 @ X44) @ X45) | ~ (r2_hidden @ X45 @ X44))),
% 1.29/1.47      inference('cnf', [status(esa)], [t4_setfam_1])).
% 1.29/1.47  thf('29', plain,
% 1.29/1.47      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 1.29/1.47      inference('sup-', [status(thm)], ['27', '28'])).
% 1.29/1.47  thf('30', plain,
% 1.29/1.47      (![X4 : $i, X6 : $i]:
% 1.29/1.47         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.29/1.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.29/1.47  thf('31', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.29/1.47          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['29', '30'])).
% 1.29/1.47  thf('32', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (((X0) = (sk_C_2 @ X0 @ (k1_tarski @ X0)))
% 1.29/1.47          | ((k1_tarski @ X0) = (k1_xboole_0))
% 1.29/1.47          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['23', '31'])).
% 1.29/1.47  thf('33', plain,
% 1.29/1.47      (![X47 : $i, X48 : $i]:
% 1.29/1.47         (((X47) = (k1_xboole_0))
% 1.29/1.47          | ~ (r1_tarski @ X48 @ (sk_C_2 @ X48 @ X47))
% 1.29/1.47          | (r1_tarski @ X48 @ (k1_setfam_1 @ X47)))),
% 1.29/1.47      inference('cnf', [status(esa)], [t6_setfam_1])).
% 1.29/1.47  thf('34', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (r1_tarski @ X0 @ X0)
% 1.29/1.47          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.29/1.47          | ((k1_tarski @ X0) = (k1_xboole_0))
% 1.29/1.47          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.29/1.47          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['32', '33'])).
% 1.29/1.47  thf('35', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.29/1.47      inference('simplify', [status(thm)], ['24'])).
% 1.29/1.47  thf('36', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.29/1.47          | ((k1_tarski @ X0) = (k1_xboole_0))
% 1.29/1.47          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.29/1.47          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 1.29/1.47      inference('demod', [status(thm)], ['34', '35'])).
% 1.29/1.47  thf('37', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         ((r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.29/1.47          | ((k1_tarski @ X0) = (k1_xboole_0))
% 1.29/1.47          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 1.29/1.47      inference('simplify', [status(thm)], ['36'])).
% 1.29/1.47  thf('38', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.29/1.47          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['29', '30'])).
% 1.29/1.47  thf('39', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.29/1.47          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 1.29/1.47      inference('clc', [status(thm)], ['37', '38'])).
% 1.29/1.47  thf(t11_setfam_1, conjecture,
% 1.29/1.47    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 1.29/1.47  thf(zf_stmt_3, negated_conjecture,
% 1.29/1.47    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 1.29/1.47    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 1.29/1.47  thf('40', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.29/1.47  thf('41', plain,
% 1.29/1.47      ((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['39', '40'])).
% 1.29/1.47  thf('42', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 1.29/1.47      inference('simplify', [status(thm)], ['41'])).
% 1.29/1.47  thf(d3_tarski, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( r1_tarski @ A @ B ) <=>
% 1.29/1.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.29/1.47  thf('43', plain,
% 1.29/1.47      (![X1 : $i, X3 : $i]:
% 1.29/1.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.29/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.29/1.47  thf('44', plain,
% 1.29/1.47      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.29/1.47         ((r2_hidden @ X38 @ X39)
% 1.29/1.47          | ~ (r2_hidden @ X38 @ (k4_xboole_0 @ X39 @ (k1_tarski @ X40))))),
% 1.29/1.47      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 1.29/1.47  thf('45', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.47         ((r1_tarski @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X2)
% 1.29/1.47          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))) @ 
% 1.29/1.47             X1))),
% 1.29/1.47      inference('sup-', [status(thm)], ['43', '44'])).
% 1.29/1.47  thf('46', plain,
% 1.29/1.47      (![X1 : $i, X3 : $i]:
% 1.29/1.47         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.29/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.29/1.47  thf('47', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         ((r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)
% 1.29/1.47          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0))),
% 1.29/1.47      inference('sup-', [status(thm)], ['45', '46'])).
% 1.29/1.47  thf('48', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)),
% 1.29/1.47      inference('simplify', [status(thm)], ['47'])).
% 1.29/1.47  thf('49', plain,
% 1.29/1.47      (![X4 : $i, X6 : $i]:
% 1.29/1.47         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.29/1.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.29/1.47  thf('50', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 1.29/1.47          | ((X0) = (k4_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['48', '49'])).
% 1.29/1.47  thf('51', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 1.29/1.47          | ((X0) = (k4_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['42', '50'])).
% 1.29/1.47  thf('52', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 1.29/1.47      inference('simplify', [status(thm)], ['41'])).
% 1.29/1.47  thf('53', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 1.29/1.47          | ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.29/1.47      inference('demod', [status(thm)], ['51', '52'])).
% 1.29/1.47  thf('54', plain,
% 1.29/1.47      (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 1.29/1.47      inference('sup-', [status(thm)], ['17', '53'])).
% 1.29/1.47  thf('55', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 1.29/1.47      inference('simplify', [status(thm)], ['41'])).
% 1.29/1.47  thf('56', plain,
% 1.29/1.47      (![X35 : $i, X36 : $i]:
% 1.29/1.47         (((X36) != (X35))
% 1.29/1.47          | ((k4_xboole_0 @ (k1_tarski @ X36) @ (k1_tarski @ X35))
% 1.29/1.47              != (k1_tarski @ X36)))),
% 1.29/1.47      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 1.29/1.47  thf('57', plain,
% 1.29/1.47      (![X35 : $i]:
% 1.29/1.47         ((k4_xboole_0 @ (k1_tarski @ X35) @ (k1_tarski @ X35))
% 1.29/1.47           != (k1_tarski @ X35))),
% 1.29/1.47      inference('simplify', [status(thm)], ['56'])).
% 1.29/1.47  thf('58', plain,
% 1.29/1.47      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) != (k1_tarski @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['55', '57'])).
% 1.29/1.47  thf('59', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 1.29/1.47      inference('simplify', [status(thm)], ['41'])).
% 1.29/1.47  thf('60', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 1.29/1.47      inference('simplify', [status(thm)], ['41'])).
% 1.29/1.47  thf('61', plain,
% 1.29/1.47      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 1.29/1.47      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.29/1.47  thf('62', plain, ($false),
% 1.29/1.47      inference('simplify_reflect-', [status(thm)], ['54', '61'])).
% 1.29/1.47  
% 1.29/1.47  % SZS output end Refutation
% 1.29/1.47  
% 1.29/1.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

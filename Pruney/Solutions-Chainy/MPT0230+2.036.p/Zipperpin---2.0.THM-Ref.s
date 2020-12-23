%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t4iBqKgUNs

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:15 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 111 expanded)
%              Number of leaves         :   35 (  48 expanded)
%              Depth                    :   16
%              Number of atoms          :  668 ( 822 expanded)
%              Number of equality atoms :   78 (  99 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( X14 = X15 )
      | ( X14 = X16 )
      | ( X14 = X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','19','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','23'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('26',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('29',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k3_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 )
      = ( k2_enumset1 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('30',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( k2_enumset1 @ X44 @ X44 @ X45 @ X46 )
      = ( k1_enumset1 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( k2_enumset1 @ X44 @ X44 @ X45 @ X46 )
      = ( k1_enumset1 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('33',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k3_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 ) @ ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_enumset1 @ X42 @ X42 @ X43 )
      = ( k2_tarski @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('38',plain,(
    ! [X69: $i,X70: $i,X71: $i] :
      ( ( k1_enumset1 @ X69 @ X71 @ X70 )
      = ( k1_enumset1 @ X69 @ X70 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('39',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X35 @ X34 @ X33 )
      = ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['28','37','40'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X18 @ X22 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X13 @ X15 @ X16 @ X13 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_enumset1 @ X42 @ X42 @ X43 )
      = ( k2_tarski @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('49',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( zip_tseitin_0 @ X23 @ X19 @ X20 @ X21 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X19 @ X20 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['0','52'])).

thf('54',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('56',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t4iBqKgUNs
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:54:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.58/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.82  % Solved by: fo/fo7.sh
% 0.58/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.82  % done 867 iterations in 0.355s
% 0.58/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.82  % SZS output start Refutation
% 0.58/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.82  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.82  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.82  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.58/0.82  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.58/0.82  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.58/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.82  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.58/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.82  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.58/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.82  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.82  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.82  thf(d1_enumset1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.82     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.58/0.82       ( ![E:$i]:
% 0.58/0.82         ( ( r2_hidden @ E @ D ) <=>
% 0.58/0.82           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.58/0.82  thf(zf_stmt_0, axiom,
% 0.58/0.82    (![E:$i,C:$i,B:$i,A:$i]:
% 0.58/0.82     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.58/0.82       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.58/0.82  thf('0', plain,
% 0.58/0.82      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.82         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 0.58/0.82          | ((X14) = (X15))
% 0.58/0.82          | ((X14) = (X16))
% 0.58/0.82          | ((X14) = (X17)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(t25_zfmisc_1, conjecture,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.58/0.82          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.58/0.82  thf(zf_stmt_1, negated_conjecture,
% 0.58/0.82    (~( ![A:$i,B:$i,C:$i]:
% 0.58/0.82        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.58/0.82             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.58/0.82    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.58/0.82  thf('1', plain,
% 0.58/0.82      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.82  thf(t28_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.58/0.82  thf('2', plain,
% 0.58/0.82      (![X5 : $i, X6 : $i]:
% 0.58/0.82         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.58/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.82  thf('3', plain,
% 0.58/0.82      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.58/0.82         = (k1_tarski @ sk_A))),
% 0.58/0.82      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.82  thf(t100_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.58/0.82  thf('4', plain,
% 0.58/0.82      (![X3 : $i, X4 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X3 @ X4)
% 0.58/0.82           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.82  thf('5', plain,
% 0.58/0.82      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.58/0.82         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['3', '4'])).
% 0.58/0.82  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.58/0.82  thf('6', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.58/0.82      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.82  thf('7', plain,
% 0.58/0.82      (![X5 : $i, X6 : $i]:
% 0.58/0.82         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.58/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.82  thf('8', plain,
% 0.58/0.82      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['6', '7'])).
% 0.58/0.82  thf(commutativity_k3_xboole_0, axiom,
% 0.58/0.82    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.58/0.82  thf('9', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.82  thf('10', plain,
% 0.58/0.82      (![X3 : $i, X4 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X3 @ X4)
% 0.58/0.82           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.82  thf('11', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X0 @ X1)
% 0.58/0.82           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['9', '10'])).
% 0.58/0.82  thf('12', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['8', '11'])).
% 0.58/0.82  thf(t5_boole, axiom,
% 0.58/0.82    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.58/0.82  thf('13', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.58/0.82      inference('cnf', [status(esa)], [t5_boole])).
% 0.58/0.82  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.82  thf(t48_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.58/0.82  thf('15', plain,
% 0.58/0.82      (![X8 : $i, X9 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.58/0.82           = (k3_xboole_0 @ X8 @ X9))),
% 0.58/0.82      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.82  thf('16', plain,
% 0.58/0.82      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['14', '15'])).
% 0.58/0.82  thf(idempotence_k3_xboole_0, axiom,
% 0.58/0.82    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.58/0.82  thf('17', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.58/0.82      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.58/0.82  thf('18', plain,
% 0.58/0.82      (![X3 : $i, X4 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X3 @ X4)
% 0.58/0.82           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.82  thf('19', plain,
% 0.58/0.82      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['17', '18'])).
% 0.58/0.82  thf('20', plain,
% 0.58/0.82      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['6', '7'])).
% 0.58/0.82  thf('21', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.82  thf('22', plain,
% 0.58/0.82      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['20', '21'])).
% 0.58/0.82  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['16', '19', '22'])).
% 0.58/0.82  thf('24', plain,
% 0.58/0.82      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.58/0.82         = (k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['5', '23'])).
% 0.58/0.82  thf(t98_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.58/0.82  thf('25', plain,
% 0.58/0.82      (![X11 : $i, X12 : $i]:
% 0.58/0.82         ((k2_xboole_0 @ X11 @ X12)
% 0.58/0.82           = (k5_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.58/0.82  thf('26', plain,
% 0.58/0.82      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.58/0.82         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['24', '25'])).
% 0.58/0.82  thf('27', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.58/0.82      inference('cnf', [status(esa)], [t5_boole])).
% 0.58/0.82  thf('28', plain,
% 0.58/0.82      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.58/0.82         = (k2_tarski @ sk_B @ sk_C))),
% 0.58/0.82      inference('demod', [status(thm)], ['26', '27'])).
% 0.58/0.82  thf(t72_enumset1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.82     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.58/0.82  thf('29', plain,
% 0.58/0.82      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.58/0.82         ((k3_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50)
% 0.58/0.82           = (k2_enumset1 @ X47 @ X48 @ X49 @ X50))),
% 0.58/0.82      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.58/0.82  thf(t71_enumset1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.58/0.82  thf('30', plain,
% 0.58/0.82      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.58/0.82         ((k2_enumset1 @ X44 @ X44 @ X45 @ X46)
% 0.58/0.82           = (k1_enumset1 @ X44 @ X45 @ X46))),
% 0.58/0.82      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.58/0.82  thf('31', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['29', '30'])).
% 0.58/0.82  thf('32', plain,
% 0.58/0.82      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.58/0.82         ((k2_enumset1 @ X44 @ X44 @ X45 @ X46)
% 0.58/0.82           = (k1_enumset1 @ X44 @ X45 @ X46))),
% 0.58/0.82      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.58/0.82  thf(t50_enumset1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.58/0.82     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.58/0.82       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.58/0.82  thf('33', plain,
% 0.58/0.82      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.58/0.82         ((k3_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40)
% 0.58/0.82           = (k2_xboole_0 @ (k2_enumset1 @ X36 @ X37 @ X38 @ X39) @ 
% 0.58/0.82              (k1_tarski @ X40)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.58/0.82  thf('34', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.82         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.58/0.82           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['32', '33'])).
% 0.58/0.82  thf('35', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.58/0.82           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['31', '34'])).
% 0.58/0.82  thf(t70_enumset1, axiom,
% 0.58/0.82    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.58/0.82  thf('36', plain,
% 0.58/0.82      (![X42 : $i, X43 : $i]:
% 0.58/0.82         ((k1_enumset1 @ X42 @ X42 @ X43) = (k2_tarski @ X42 @ X43))),
% 0.58/0.82      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.82  thf('37', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.58/0.82           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['35', '36'])).
% 0.58/0.82  thf(t98_enumset1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.58/0.82  thf('38', plain,
% 0.58/0.82      (![X69 : $i, X70 : $i, X71 : $i]:
% 0.58/0.82         ((k1_enumset1 @ X69 @ X71 @ X70) = (k1_enumset1 @ X69 @ X70 @ X71))),
% 0.58/0.82      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.58/0.82  thf(t102_enumset1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.58/0.82  thf('39', plain,
% 0.58/0.82      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.58/0.82         ((k1_enumset1 @ X35 @ X34 @ X33) = (k1_enumset1 @ X33 @ X34 @ X35))),
% 0.58/0.82      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.58/0.82  thf('40', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['38', '39'])).
% 0.58/0.82  thf('41', plain,
% 0.58/0.82      (((k1_enumset1 @ sk_A @ sk_B @ sk_C) = (k2_tarski @ sk_B @ sk_C))),
% 0.58/0.82      inference('demod', [status(thm)], ['28', '37', '40'])).
% 0.58/0.82  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.58/0.82  thf(zf_stmt_3, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.82     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.58/0.82       ( ![E:$i]:
% 0.58/0.82         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.58/0.82  thf('42', plain,
% 0.58/0.82      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.58/0.82         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 0.58/0.82          | (r2_hidden @ X18 @ X22)
% 0.58/0.82          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.82  thf('43', plain,
% 0.58/0.82      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.58/0.82         ((r2_hidden @ X18 @ (k1_enumset1 @ X21 @ X20 @ X19))
% 0.58/0.82          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 0.58/0.82      inference('simplify', [status(thm)], ['42'])).
% 0.58/0.82  thf('44', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 0.58/0.82          | (zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A))),
% 0.58/0.82      inference('sup+', [status(thm)], ['41', '43'])).
% 0.58/0.82  thf('45', plain,
% 0.58/0.82      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.58/0.82         (((X14) != (X13)) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('46', plain,
% 0.58/0.82      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.58/0.82         ~ (zip_tseitin_0 @ X13 @ X15 @ X16 @ X13)),
% 0.58/0.82      inference('simplify', [status(thm)], ['45'])).
% 0.58/0.82  thf('47', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C))),
% 0.58/0.82      inference('sup-', [status(thm)], ['44', '46'])).
% 0.58/0.82  thf('48', plain,
% 0.58/0.82      (![X42 : $i, X43 : $i]:
% 0.58/0.82         ((k1_enumset1 @ X42 @ X42 @ X43) = (k2_tarski @ X42 @ X43))),
% 0.58/0.82      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.82  thf('49', plain,
% 0.58/0.82      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.58/0.82         (~ (r2_hidden @ X23 @ X22)
% 0.58/0.82          | ~ (zip_tseitin_0 @ X23 @ X19 @ X20 @ X21)
% 0.58/0.82          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.82  thf('50', plain,
% 0.58/0.82      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 0.58/0.82         (~ (zip_tseitin_0 @ X23 @ X19 @ X20 @ X21)
% 0.58/0.82          | ~ (r2_hidden @ X23 @ (k1_enumset1 @ X21 @ X20 @ X19)))),
% 0.58/0.82      inference('simplify', [status(thm)], ['49'])).
% 0.58/0.82  thf('51', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.58/0.82          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.58/0.82      inference('sup-', [status(thm)], ['48', '50'])).
% 0.58/0.82  thf('52', plain, (~ (zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B)),
% 0.58/0.82      inference('sup-', [status(thm)], ['47', '51'])).
% 0.58/0.82  thf('53', plain,
% 0.58/0.82      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_C)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['0', '52'])).
% 0.58/0.82  thf('54', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.58/0.82      inference('simplify', [status(thm)], ['53'])).
% 0.58/0.82  thf('55', plain, (((sk_A) != (sk_B))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.82  thf('56', plain, (((sk_A) != (sk_C))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.82  thf('57', plain, ($false),
% 0.58/0.82      inference('simplify_reflect-', [status(thm)], ['54', '55', '56'])).
% 0.58/0.82  
% 0.58/0.82  % SZS output end Refutation
% 0.58/0.82  
% 0.65/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

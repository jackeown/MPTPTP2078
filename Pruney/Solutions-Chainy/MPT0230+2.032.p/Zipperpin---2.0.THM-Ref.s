%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SmQo4tcVKP

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:14 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 104 expanded)
%              Number of leaves         :   36 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  642 ( 760 expanded)
%              Number of equality atoms :   80 (  96 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('16',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','22'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('25',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('28',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k3_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 )
      = ( k2_enumset1 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('29',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X42 @ X42 @ X43 @ X44 )
      = ( k1_enumset1 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X42 @ X42 @ X43 @ X44 )
      = ( k1_enumset1 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('32',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k3_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) @ ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('37',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ( k1_enumset1 @ X67 @ X69 @ X68 )
      = ( k1_enumset1 @ X67 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('38',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X33 @ X32 @ X31 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['27','36','39'])).

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

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X18 @ X22 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['40','42'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('44',plain,(
    ! [X25: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X27 )
      | ( X29 = X28 )
      | ( X29 = X25 )
      | ( X27
       != ( k2_tarski @ X28 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('45',plain,(
    ! [X25: $i,X28: $i,X29: $i] :
      ( ( X29 = X25 )
      | ( X29 = X28 )
      | ~ ( r2_hidden @ X29 @ ( k2_tarski @ X28 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A )
      | ( X0 = sk_B )
      | ( X0 = sk_C ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('48',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X13 @ X15 @ X16 @ X13 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SmQo4tcVKP
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:43:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.66/0.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.91  % Solved by: fo/fo7.sh
% 0.66/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.91  % done 1073 iterations in 0.445s
% 0.66/0.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.91  % SZS output start Refutation
% 0.66/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.91  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.66/0.91  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.66/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.91  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.66/0.91  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.66/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.66/0.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.66/0.91  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.66/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.66/0.91  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.91  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.66/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.91  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.66/0.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.66/0.91  thf(t25_zfmisc_1, conjecture,
% 0.66/0.91    (![A:$i,B:$i,C:$i]:
% 0.66/0.91     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.66/0.91          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.66/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.91    (~( ![A:$i,B:$i,C:$i]:
% 0.66/0.91        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.66/0.91             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.66/0.91    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.66/0.91  thf('0', plain,
% 0.66/0.91      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf(t28_xboole_1, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.66/0.91  thf('1', plain,
% 0.66/0.91      (![X5 : $i, X6 : $i]:
% 0.66/0.91         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.66/0.91      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.66/0.91  thf('2', plain,
% 0.66/0.91      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.66/0.91         = (k1_tarski @ sk_A))),
% 0.66/0.91      inference('sup-', [status(thm)], ['0', '1'])).
% 0.66/0.91  thf(t100_xboole_1, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.66/0.91  thf('3', plain,
% 0.66/0.91      (![X3 : $i, X4 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X3 @ X4)
% 0.66/0.91           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.91  thf('4', plain,
% 0.66/0.91      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.66/0.91         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['2', '3'])).
% 0.66/0.91  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.66/0.91  thf('5', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.66/0.91      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.66/0.91  thf('6', plain,
% 0.66/0.91      (![X5 : $i, X6 : $i]:
% 0.66/0.91         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.66/0.91      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.66/0.91  thf('7', plain,
% 0.66/0.91      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['5', '6'])).
% 0.66/0.91  thf(commutativity_k3_xboole_0, axiom,
% 0.66/0.91    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.66/0.91  thf('8', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.91  thf('9', plain,
% 0.66/0.91      (![X3 : $i, X4 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X3 @ X4)
% 0.66/0.91           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.91  thf('10', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X0 @ X1)
% 0.66/0.91           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['8', '9'])).
% 0.66/0.91  thf('11', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['7', '10'])).
% 0.66/0.91  thf(t5_boole, axiom,
% 0.66/0.91    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.66/0.91  thf('12', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.66/0.91      inference('cnf', [status(esa)], [t5_boole])).
% 0.66/0.91  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['11', '12'])).
% 0.66/0.91  thf(t48_xboole_1, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.66/0.91  thf('14', plain,
% 0.66/0.91      (![X8 : $i, X9 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.66/0.91           = (k3_xboole_0 @ X8 @ X9))),
% 0.66/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.91  thf('15', plain,
% 0.66/0.91      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['13', '14'])).
% 0.66/0.91  thf(idempotence_k3_xboole_0, axiom,
% 0.66/0.91    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.66/0.91  thf('16', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.66/0.91      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.66/0.91  thf('17', plain,
% 0.66/0.91      (![X3 : $i, X4 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X3 @ X4)
% 0.66/0.91           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.91  thf('18', plain,
% 0.66/0.91      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['16', '17'])).
% 0.66/0.91  thf('19', plain,
% 0.66/0.91      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['5', '6'])).
% 0.66/0.91  thf('20', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.91  thf('21', plain,
% 0.66/0.91      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['19', '20'])).
% 0.66/0.91  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.66/0.91      inference('demod', [status(thm)], ['15', '18', '21'])).
% 0.66/0.91  thf('23', plain,
% 0.66/0.91      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.66/0.91         = (k1_xboole_0))),
% 0.66/0.91      inference('demod', [status(thm)], ['4', '22'])).
% 0.66/0.91  thf(t98_xboole_1, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.66/0.91  thf('24', plain,
% 0.66/0.91      (![X11 : $i, X12 : $i]:
% 0.66/0.91         ((k2_xboole_0 @ X11 @ X12)
% 0.66/0.91           = (k5_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.66/0.91  thf('25', plain,
% 0.66/0.91      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.66/0.91         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['23', '24'])).
% 0.66/0.91  thf('26', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.66/0.91      inference('cnf', [status(esa)], [t5_boole])).
% 0.66/0.91  thf('27', plain,
% 0.66/0.91      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.66/0.91         = (k2_tarski @ sk_B @ sk_C))),
% 0.66/0.91      inference('demod', [status(thm)], ['25', '26'])).
% 0.66/0.91  thf(t72_enumset1, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.91     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.66/0.91  thf('28', plain,
% 0.66/0.91      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.66/0.91         ((k3_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48)
% 0.66/0.91           = (k2_enumset1 @ X45 @ X46 @ X47 @ X48))),
% 0.66/0.91      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.66/0.91  thf(t71_enumset1, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i]:
% 0.66/0.91     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.66/0.91  thf('29', plain,
% 0.66/0.91      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.66/0.91         ((k2_enumset1 @ X42 @ X42 @ X43 @ X44)
% 0.66/0.91           = (k1_enumset1 @ X42 @ X43 @ X44))),
% 0.66/0.91      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.66/0.91  thf('30', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['28', '29'])).
% 0.66/0.91  thf('31', plain,
% 0.66/0.91      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.66/0.91         ((k2_enumset1 @ X42 @ X42 @ X43 @ X44)
% 0.66/0.91           = (k1_enumset1 @ X42 @ X43 @ X44))),
% 0.66/0.91      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.66/0.91  thf(t50_enumset1, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.66/0.91     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.66/0.91       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.66/0.91  thf('32', plain,
% 0.66/0.91      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.66/0.91         ((k3_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38)
% 0.66/0.91           = (k2_xboole_0 @ (k2_enumset1 @ X34 @ X35 @ X36 @ X37) @ 
% 0.66/0.91              (k1_tarski @ X38)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.66/0.91  thf('33', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.91         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.66/0.91           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['31', '32'])).
% 0.66/0.91  thf('34', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.66/0.91           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['30', '33'])).
% 0.66/0.91  thf(t70_enumset1, axiom,
% 0.66/0.91    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.66/0.91  thf('35', plain,
% 0.66/0.91      (![X40 : $i, X41 : $i]:
% 0.66/0.91         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 0.66/0.91      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.66/0.91  thf('36', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.66/0.91           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.66/0.91      inference('demod', [status(thm)], ['34', '35'])).
% 0.66/0.91  thf(t98_enumset1, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i]:
% 0.66/0.91     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.66/0.91  thf('37', plain,
% 0.66/0.91      (![X67 : $i, X68 : $i, X69 : $i]:
% 0.66/0.91         ((k1_enumset1 @ X67 @ X69 @ X68) = (k1_enumset1 @ X67 @ X68 @ X69))),
% 0.66/0.91      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.66/0.91  thf(t102_enumset1, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i]:
% 0.66/0.91     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.66/0.91  thf('38', plain,
% 0.66/0.91      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.66/0.91         ((k1_enumset1 @ X33 @ X32 @ X31) = (k1_enumset1 @ X31 @ X32 @ X33))),
% 0.66/0.91      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.66/0.91  thf('39', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['37', '38'])).
% 0.66/0.91  thf('40', plain,
% 0.66/0.91      (((k1_enumset1 @ sk_A @ sk_B @ sk_C) = (k2_tarski @ sk_B @ sk_C))),
% 0.66/0.91      inference('demod', [status(thm)], ['27', '36', '39'])).
% 0.66/0.91  thf(d1_enumset1, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.91     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.66/0.91       ( ![E:$i]:
% 0.66/0.91         ( ( r2_hidden @ E @ D ) <=>
% 0.66/0.91           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.66/0.91  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.66/0.91  thf(zf_stmt_2, axiom,
% 0.66/0.91    (![E:$i,C:$i,B:$i,A:$i]:
% 0.66/0.91     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.66/0.91       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.66/0.91  thf(zf_stmt_3, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.91     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.66/0.91       ( ![E:$i]:
% 0.66/0.91         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.66/0.91  thf('41', plain,
% 0.66/0.91      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.66/0.91         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 0.66/0.91          | (r2_hidden @ X18 @ X22)
% 0.66/0.91          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.66/0.91  thf('42', plain,
% 0.66/0.91      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.66/0.91         ((r2_hidden @ X18 @ (k1_enumset1 @ X21 @ X20 @ X19))
% 0.66/0.91          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 0.66/0.91      inference('simplify', [status(thm)], ['41'])).
% 0.66/0.91  thf('43', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 0.66/0.91          | (zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A))),
% 0.66/0.91      inference('sup+', [status(thm)], ['40', '42'])).
% 0.66/0.91  thf(d2_tarski, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i]:
% 0.66/0.91     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.66/0.91       ( ![D:$i]:
% 0.66/0.91         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.66/0.91  thf('44', plain,
% 0.66/0.91      (![X25 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X29 @ X27)
% 0.66/0.91          | ((X29) = (X28))
% 0.66/0.91          | ((X29) = (X25))
% 0.66/0.91          | ((X27) != (k2_tarski @ X28 @ X25)))),
% 0.66/0.91      inference('cnf', [status(esa)], [d2_tarski])).
% 0.66/0.91  thf('45', plain,
% 0.66/0.91      (![X25 : $i, X28 : $i, X29 : $i]:
% 0.66/0.91         (((X29) = (X25))
% 0.66/0.91          | ((X29) = (X28))
% 0.66/0.91          | ~ (r2_hidden @ X29 @ (k2_tarski @ X28 @ X25)))),
% 0.66/0.91      inference('simplify', [status(thm)], ['44'])).
% 0.66/0.91  thf('46', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A)
% 0.66/0.91          | ((X0) = (sk_B))
% 0.66/0.91          | ((X0) = (sk_C)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['43', '45'])).
% 0.66/0.91  thf('47', plain,
% 0.66/0.91      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.66/0.91         (((X14) != (X13)) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.66/0.91  thf('48', plain,
% 0.66/0.91      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.66/0.91         ~ (zip_tseitin_0 @ X13 @ X15 @ X16 @ X13)),
% 0.66/0.91      inference('simplify', [status(thm)], ['47'])).
% 0.66/0.91  thf('49', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['46', '48'])).
% 0.66/0.91  thf('50', plain, (((sk_A) != (sk_B))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf('51', plain, (((sk_A) != (sk_C))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf('52', plain, ($false),
% 0.66/0.91      inference('simplify_reflect-', [status(thm)], ['49', '50', '51'])).
% 0.66/0.91  
% 0.66/0.91  % SZS output end Refutation
% 0.66/0.91  
% 0.66/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

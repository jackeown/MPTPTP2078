%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qksmoAfCQB

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:37 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 102 expanded)
%              Number of leaves         :   37 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :  633 ( 741 expanded)
%              Number of equality atoms :   72 (  88 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( X24 = X25 )
      | ( X24 = X26 )
      | ( X24 = X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X67: $i,X68: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X67 ) @ ( k2_tarski @ X67 @ X68 ) )
      = ( k1_tarski @ X67 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('14',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','26'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('29',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('31',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('32',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('33',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('34',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_xboole_0 @ ( k2_tarski @ X35 @ X36 ) @ ( k2_tarski @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('36',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X42 @ X42 @ X43 @ X44 )
      = ( k1_enumset1 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('37',plain,
    ( ( k1_enumset1 @ sk_A @ sk_C @ sk_D )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['32','35','36'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 )
      | ( r2_hidden @ X28 @ X32 )
      | ( X32
       != ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X28 @ ( k1_enumset1 @ X31 @ X30 @ X29 ) )
      | ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_C @ sk_D ) )
      | ( zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','39'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('42',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X32 )
      | ~ ( zip_tseitin_0 @ X33 @ X29 @ X30 @ X31 )
      | ( X32
       != ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    ! [X29: $i,X30: $i,X31: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X29 @ X30 @ X31 )
      | ~ ( r2_hidden @ X33 @ ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_A )
      | ~ ( zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_C )
      | ( X0 = sk_C )
      | ( X0 = sk_D )
      | ( zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_A )
      | ( X0 = sk_D )
      | ( X0 = sk_C ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X24 != X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ~ ( zip_tseitin_0 @ X23 @ X25 @ X26 @ X23 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('52',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qksmoAfCQB
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 534 iterations in 0.191s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.45/0.65  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.45/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.65  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.65  thf(d1_enumset1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.65       ( ![E:$i]:
% 0.45/0.65         ( ( r2_hidden @ E @ D ) <=>
% 0.45/0.65           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, axiom,
% 0.45/0.65    (![E:$i,C:$i,B:$i,A:$i]:
% 0.45/0.65     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.45/0.65       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.65         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 0.45/0.65          | ((X24) = (X25))
% 0.45/0.65          | ((X24) = (X26))
% 0.45/0.65          | ((X24) = (X27)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t28_zfmisc_1, conjecture,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.45/0.65          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_1, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.45/0.65             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.65  thf(t19_zfmisc_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.45/0.65       ( k1_tarski @ A ) ))).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X67 : $i, X68 : $i]:
% 0.45/0.65         ((k3_xboole_0 @ (k1_tarski @ X67) @ (k2_tarski @ X67 @ X68))
% 0.45/0.65           = (k1_tarski @ X67))),
% 0.45/0.65      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.45/0.65  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.65  thf(t17_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.45/0.65      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.45/0.65      inference('sup+', [status(thm)], ['3', '4'])).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))),
% 0.45/0.65      inference('sup+', [status(thm)], ['2', '5'])).
% 0.45/0.65  thf(t1_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.45/0.65       ( r1_tarski @ A @ C ) ))).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.65         (~ (r1_tarski @ X12 @ X13)
% 0.45/0.65          | ~ (r1_tarski @ X13 @ X14)
% 0.45/0.65          | (r1_tarski @ X12 @ X14))),
% 0.45/0.65      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         ((r1_tarski @ (k1_tarski @ X1) @ X2)
% 0.45/0.65          | ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.45/0.65      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))),
% 0.45/0.65      inference('sup-', [status(thm)], ['1', '8'])).
% 0.45/0.65  thf(t28_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      (![X15 : $i, X16 : $i]:
% 0.45/0.65         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.45/0.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 0.45/0.65         = (k1_tarski @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf(t100_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X8 : $i, X9 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X8 @ X9)
% 0.45/0.65           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 0.45/0.65         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['11', '12'])).
% 0.45/0.65  thf(idempotence_k3_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.45/0.65  thf('14', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (![X8 : $i, X9 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X8 @ X9)
% 0.45/0.65           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['14', '15'])).
% 0.45/0.65  thf(t2_boole, axiom,
% 0.45/0.65    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t2_boole])).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (![X8 : $i, X9 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X8 @ X9)
% 0.45/0.65           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.65  thf(t5_boole, axiom,
% 0.45/0.65    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.65  thf('20', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.45/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.65  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.65      inference('demod', [status(thm)], ['19', '20'])).
% 0.45/0.65  thf(t48_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.65  thf('22', plain,
% 0.45/0.65      (![X18 : $i, X19 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.45/0.65           = (k3_xboole_0 @ X18 @ X19))),
% 0.45/0.65      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['21', '22'])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t2_boole])).
% 0.45/0.65  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['23', '24'])).
% 0.45/0.65  thf('26', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['16', '25'])).
% 0.45/0.65  thf('27', plain,
% 0.45/0.65      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 0.45/0.65         = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['13', '26'])).
% 0.45/0.65  thf(t98_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      (![X21 : $i, X22 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X21 @ X22)
% 0.45/0.65           = (k5_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      (((k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ (k1_tarski @ sk_A))
% 0.45/0.65         = (k5_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ k1_xboole_0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['27', '28'])).
% 0.45/0.65  thf(commutativity_k2_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.45/0.65  thf('30', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.65  thf('31', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.45/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 0.45/0.65         = (k2_tarski @ sk_C @ sk_D))),
% 0.45/0.65      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.45/0.65  thf(t69_enumset1, axiom,
% 0.45/0.65    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 0.45/0.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.65  thf(l53_enumset1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.45/0.65       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.45/0.65  thf('34', plain,
% 0.45/0.65      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.45/0.65         ((k2_enumset1 @ X35 @ X36 @ X37 @ X38)
% 0.45/0.65           = (k2_xboole_0 @ (k2_tarski @ X35 @ X36) @ (k2_tarski @ X37 @ X38)))),
% 0.45/0.65      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.45/0.65  thf('35', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.45/0.65           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['33', '34'])).
% 0.45/0.65  thf(t71_enumset1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.45/0.65  thf('36', plain,
% 0.45/0.65      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.45/0.65         ((k2_enumset1 @ X42 @ X42 @ X43 @ X44)
% 0.45/0.65           = (k1_enumset1 @ X42 @ X43 @ X44))),
% 0.45/0.65      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      (((k1_enumset1 @ sk_A @ sk_C @ sk_D) = (k2_tarski @ sk_C @ sk_D))),
% 0.45/0.65      inference('demod', [status(thm)], ['32', '35', '36'])).
% 0.45/0.65  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.45/0.65  thf(zf_stmt_3, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.65       ( ![E:$i]:
% 0.45/0.65         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.45/0.65  thf('38', plain,
% 0.45/0.65      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.45/0.65         ((zip_tseitin_0 @ X28 @ X29 @ X30 @ X31)
% 0.45/0.65          | (r2_hidden @ X28 @ X32)
% 0.45/0.65          | ((X32) != (k1_enumset1 @ X31 @ X30 @ X29)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.65  thf('39', plain,
% 0.45/0.65      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.45/0.65         ((r2_hidden @ X28 @ (k1_enumset1 @ X31 @ X30 @ X29))
% 0.45/0.65          | (zip_tseitin_0 @ X28 @ X29 @ X30 @ X31))),
% 0.45/0.65      inference('simplify', [status(thm)], ['38'])).
% 0.45/0.65  thf('40', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((r2_hidden @ X0 @ (k2_tarski @ sk_C @ sk_D))
% 0.45/0.65          | (zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_A))),
% 0.45/0.65      inference('sup+', [status(thm)], ['37', '39'])).
% 0.45/0.65  thf(t70_enumset1, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.65  thf('41', plain,
% 0.45/0.65      (![X40 : $i, X41 : $i]:
% 0.45/0.65         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 0.45/0.65      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.65  thf('42', plain,
% 0.45/0.65      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X33 @ X32)
% 0.45/0.65          | ~ (zip_tseitin_0 @ X33 @ X29 @ X30 @ X31)
% 0.45/0.65          | ((X32) != (k1_enumset1 @ X31 @ X30 @ X29)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.65  thf('43', plain,
% 0.45/0.65      (![X29 : $i, X30 : $i, X31 : $i, X33 : $i]:
% 0.45/0.65         (~ (zip_tseitin_0 @ X33 @ X29 @ X30 @ X31)
% 0.45/0.65          | ~ (r2_hidden @ X33 @ (k1_enumset1 @ X31 @ X30 @ X29)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['42'])).
% 0.45/0.65  thf('44', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.45/0.65          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['41', '43'])).
% 0.45/0.65  thf('45', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_A)
% 0.45/0.65          | ~ (zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['40', '44'])).
% 0.45/0.65  thf('46', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((X0) = (sk_C))
% 0.45/0.65          | ((X0) = (sk_C))
% 0.45/0.65          | ((X0) = (sk_D))
% 0.45/0.65          | (zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['0', '45'])).
% 0.45/0.65  thf('47', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_A)
% 0.45/0.65          | ((X0) = (sk_D))
% 0.45/0.65          | ((X0) = (sk_C)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['46'])).
% 0.45/0.65  thf('48', plain,
% 0.45/0.65      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.65         (((X24) != (X23)) | ~ (zip_tseitin_0 @ X24 @ X25 @ X26 @ X23))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('49', plain,
% 0.45/0.65      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.45/0.65         ~ (zip_tseitin_0 @ X23 @ X25 @ X26 @ X23)),
% 0.45/0.65      inference('simplify', [status(thm)], ['48'])).
% 0.45/0.65  thf('50', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_D)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['47', '49'])).
% 0.45/0.65  thf('51', plain, (((sk_A) != (sk_D))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.65  thf('52', plain, (((sk_A) != (sk_C))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.65  thf('53', plain, ($false),
% 0.45/0.65      inference('simplify_reflect-', [status(thm)], ['50', '51', '52'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.49/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

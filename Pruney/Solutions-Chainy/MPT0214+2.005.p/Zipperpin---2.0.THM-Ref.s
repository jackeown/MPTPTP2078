%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BQ5D6zy3mt

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:45 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 125 expanded)
%              Number of leaves         :   35 (  51 expanded)
%              Depth                    :   18
%              Number of atoms          :  621 ( 922 expanded)
%              Number of equality atoms :   64 (  97 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t6_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t6_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('13',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('21',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','23'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('26',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('29',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('31',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X36 @ X37 @ X38 ) @ ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('34',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('35',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ( k2_tarski @ sk_B_1 @ sk_A )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
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

thf('40',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( r2_hidden @ X24 @ X28 )
      | ( X28
       != ( k1_enumset1 @ X27 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X24 @ ( k1_enumset1 @ X27 @ X26 @ X25 ) )
      | ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X20 != X21 )
      | ~ ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('44',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ~ ( zip_tseitin_0 @ X21 @ X21 @ X22 @ X19 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['38','45'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('47',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X34 @ X33 )
      | ( X34 = X31 )
      | ( X33
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('48',plain,(
    ! [X31: $i,X34: $i] :
      ( ( X34 = X31 )
      | ~ ( r2_hidden @ X34 @ ( k1_tarski @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    sk_A = sk_B_1 ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BQ5D6zy3mt
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.68  % Solved by: fo/fo7.sh
% 0.45/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.68  % done 784 iterations in 0.225s
% 0.45/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.68  % SZS output start Refutation
% 0.45/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.45/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.68  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.68  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.68  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.45/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.68  thf(t6_zfmisc_1, conjecture,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.45/0.68       ( ( A ) = ( B ) ) ))).
% 0.45/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.68    (~( ![A:$i,B:$i]:
% 0.45/0.68        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.45/0.68          ( ( A ) = ( B ) ) ) )),
% 0.45/0.68    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.45/0.68  thf('0', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(t28_xboole_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.45/0.68  thf('1', plain,
% 0.45/0.68      (![X10 : $i, X11 : $i]:
% 0.45/0.68         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.45/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.45/0.68  thf('2', plain,
% 0.45/0.68      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.45/0.68         = (k1_tarski @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.68  thf(t100_xboole_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.68  thf('3', plain,
% 0.45/0.68      (![X8 : $i, X9 : $i]:
% 0.45/0.68         ((k4_xboole_0 @ X8 @ X9)
% 0.45/0.68           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.68  thf('4', plain,
% 0.45/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.45/0.68         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['2', '3'])).
% 0.45/0.68  thf(t7_xboole_0, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.68          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.45/0.68  thf('5', plain,
% 0.45/0.68      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.45/0.68      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.68  thf('6', plain,
% 0.45/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.45/0.68         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['2', '3'])).
% 0.45/0.68  thf(t48_xboole_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.68  thf('7', plain,
% 0.45/0.68      (![X12 : $i, X13 : $i]:
% 0.45/0.68         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.45/0.68           = (k3_xboole_0 @ X12 @ X13))),
% 0.45/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.68  thf('8', plain,
% 0.45/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.45/0.68         (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.45/0.68         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.45/0.68  thf('9', plain,
% 0.45/0.68      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.45/0.68         = (k1_tarski @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.68  thf('10', plain,
% 0.45/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.45/0.68         (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.45/0.68         = (k1_tarski @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.68  thf('11', plain,
% 0.45/0.68      (![X12 : $i, X13 : $i]:
% 0.45/0.68         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.45/0.68           = (k3_xboole_0 @ X12 @ X13))),
% 0.45/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.68  thf('12', plain,
% 0.45/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.45/0.68         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.45/0.68            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.45/0.68      inference('sup+', [status(thm)], ['10', '11'])).
% 0.45/0.68  thf(idempotence_k3_xboole_0, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.45/0.68  thf('13', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.45/0.68      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.45/0.68  thf('14', plain,
% 0.45/0.68      (![X8 : $i, X9 : $i]:
% 0.45/0.68         ((k4_xboole_0 @ X8 @ X9)
% 0.45/0.68           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.68  thf('15', plain,
% 0.45/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['13', '14'])).
% 0.45/0.68  thf('16', plain,
% 0.45/0.68      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.45/0.68         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.45/0.68            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.45/0.68      inference('demod', [status(thm)], ['12', '15'])).
% 0.45/0.68  thf(t4_xboole_0, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.68            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.68       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.68            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.68  thf('17', plain,
% 0.45/0.68      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.45/0.68          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.45/0.68      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.68  thf('18', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X0 @ 
% 0.45/0.68             (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.45/0.68          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.45/0.68               (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('19', plain,
% 0.45/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.45/0.68         (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.45/0.68         = (k1_tarski @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.68  thf(t79_xboole_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.45/0.68  thf('20', plain,
% 0.45/0.68      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 0.45/0.68      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.45/0.68  thf('21', plain,
% 0.45/0.68      ((r1_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.45/0.68        (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['19', '20'])).
% 0.45/0.68  thf('22', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ~ (r2_hidden @ X0 @ 
% 0.45/0.68            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['18', '21'])).
% 0.45/0.68  thf('23', plain,
% 0.45/0.68      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['5', '22'])).
% 0.45/0.68  thf('24', plain,
% 0.45/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.45/0.68         = (k1_xboole_0))),
% 0.45/0.68      inference('demod', [status(thm)], ['4', '23'])).
% 0.45/0.68  thf(t98_xboole_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.45/0.68  thf('25', plain,
% 0.45/0.68      (![X17 : $i, X18 : $i]:
% 0.45/0.68         ((k2_xboole_0 @ X17 @ X18)
% 0.45/0.68           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.68  thf('26', plain,
% 0.45/0.68      (((k2_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.45/0.68         = (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ k1_xboole_0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['24', '25'])).
% 0.45/0.68  thf(t5_boole, axiom,
% 0.45/0.68    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.68  thf('27', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.45/0.68      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.68  thf('28', plain,
% 0.45/0.68      (((k2_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.45/0.68         = (k1_tarski @ sk_B_1))),
% 0.45/0.68      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.68  thf(t69_enumset1, axiom,
% 0.45/0.68    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.68  thf('29', plain,
% 0.45/0.68      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 0.45/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.68  thf(t70_enumset1, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.68  thf('30', plain,
% 0.45/0.68      (![X41 : $i, X42 : $i]:
% 0.45/0.68         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.45/0.68      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.68  thf(t46_enumset1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.45/0.68       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.45/0.68  thf('31', plain,
% 0.45/0.68      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.45/0.68         ((k2_enumset1 @ X36 @ X37 @ X38 @ X39)
% 0.45/0.68           = (k2_xboole_0 @ (k1_enumset1 @ X36 @ X37 @ X38) @ (k1_tarski @ X39)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.45/0.68  thf('32', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.45/0.68           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['30', '31'])).
% 0.45/0.68  thf('33', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.45/0.68           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['29', '32'])).
% 0.45/0.68  thf(t71_enumset1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.45/0.68  thf('34', plain,
% 0.45/0.68      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.45/0.68         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 0.45/0.68           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 0.45/0.68      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.68  thf('35', plain,
% 0.45/0.68      (![X41 : $i, X42 : $i]:
% 0.45/0.68         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.45/0.68      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.68  thf('36', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['34', '35'])).
% 0.45/0.68  thf('37', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((k2_tarski @ X0 @ X1)
% 0.45/0.68           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.45/0.68      inference('demod', [status(thm)], ['33', '36'])).
% 0.45/0.68  thf('38', plain, (((k2_tarski @ sk_B_1 @ sk_A) = (k1_tarski @ sk_B_1))),
% 0.45/0.68      inference('demod', [status(thm)], ['28', '37'])).
% 0.45/0.68  thf('39', plain,
% 0.45/0.68      (![X41 : $i, X42 : $i]:
% 0.45/0.68         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.45/0.68      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.68  thf(d1_enumset1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.68       ( ![E:$i]:
% 0.45/0.68         ( ( r2_hidden @ E @ D ) <=>
% 0.45/0.68           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.45/0.68  thf(zf_stmt_2, axiom,
% 0.45/0.68    (![E:$i,C:$i,B:$i,A:$i]:
% 0.45/0.68     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.45/0.68       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_3, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.68       ( ![E:$i]:
% 0.45/0.68         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.45/0.68  thf('40', plain,
% 0.45/0.68      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.68         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 0.45/0.68          | (r2_hidden @ X24 @ X28)
% 0.45/0.68          | ((X28) != (k1_enumset1 @ X27 @ X26 @ X25)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.68  thf('41', plain,
% 0.45/0.68      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.68         ((r2_hidden @ X24 @ (k1_enumset1 @ X27 @ X26 @ X25))
% 0.45/0.68          | (zip_tseitin_0 @ X24 @ X25 @ X26 @ X27))),
% 0.45/0.68      inference('simplify', [status(thm)], ['40'])).
% 0.45/0.68  thf('42', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.45/0.68          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.45/0.68      inference('sup+', [status(thm)], ['39', '41'])).
% 0.45/0.68  thf('43', plain,
% 0.45/0.68      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.68         (((X20) != (X21)) | ~ (zip_tseitin_0 @ X20 @ X21 @ X22 @ X19))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.68  thf('44', plain,
% 0.45/0.68      (![X19 : $i, X21 : $i, X22 : $i]:
% 0.45/0.68         ~ (zip_tseitin_0 @ X21 @ X21 @ X22 @ X19)),
% 0.45/0.68      inference('simplify', [status(thm)], ['43'])).
% 0.45/0.68  thf('45', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.45/0.68      inference('sup-', [status(thm)], ['42', '44'])).
% 0.45/0.68  thf('46', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.45/0.68      inference('sup+', [status(thm)], ['38', '45'])).
% 0.45/0.68  thf(d1_tarski, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.45/0.68  thf('47', plain,
% 0.45/0.68      (![X31 : $i, X33 : $i, X34 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X34 @ X33)
% 0.45/0.68          | ((X34) = (X31))
% 0.45/0.68          | ((X33) != (k1_tarski @ X31)))),
% 0.45/0.68      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.68  thf('48', plain,
% 0.45/0.68      (![X31 : $i, X34 : $i]:
% 0.45/0.68         (((X34) = (X31)) | ~ (r2_hidden @ X34 @ (k1_tarski @ X31)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['47'])).
% 0.45/0.68  thf('49', plain, (((sk_A) = (sk_B_1))),
% 0.45/0.68      inference('sup-', [status(thm)], ['46', '48'])).
% 0.45/0.68  thf('50', plain, (((sk_A) != (sk_B_1))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('51', plain, ($false),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.45/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

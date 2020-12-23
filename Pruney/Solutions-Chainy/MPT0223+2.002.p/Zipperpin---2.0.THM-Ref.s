%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TAfJR7C7K7

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:31 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 114 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  575 ( 904 expanded)
%              Number of equality atoms :   69 ( 105 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','7'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X28 @ X29 @ X30 ) @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('18',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('19',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('21',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['17','26'])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('29',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['12','27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ sk_B @ sk_B @ sk_A @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['17','26'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ sk_B @ sk_A @ X0 )
      = ( k2_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

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

thf('35',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X20 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ sk_B ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X14 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('39',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X13 @ X14 @ X11 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('42',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X25 )
      | ( X26 = X23 )
      | ( X25
       != ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('43',plain,(
    ! [X23: $i,X26: $i] :
      ( ( X26 = X23 )
      | ~ ( r2_hidden @ X26 @ ( k1_tarski @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TAfJR7C7K7
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:15:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.61  % Solved by: fo/fo7.sh
% 0.38/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.61  % done 314 iterations in 0.150s
% 0.38/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.61  % SZS output start Refutation
% 0.38/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.38/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.61  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.38/0.61  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.38/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.38/0.61  thf(t18_zfmisc_1, conjecture,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.38/0.61         ( k1_tarski @ A ) ) =>
% 0.38/0.61       ( ( A ) = ( B ) ) ))).
% 0.38/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.61    (~( ![A:$i,B:$i]:
% 0.38/0.61        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.38/0.61            ( k1_tarski @ A ) ) =>
% 0.38/0.61          ( ( A ) = ( B ) ) ) )),
% 0.38/0.61    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.38/0.61  thf('0', plain,
% 0.38/0.61      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.38/0.61         = (k1_tarski @ sk_A))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t100_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.61  thf('1', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.61           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.61  thf('2', plain,
% 0.38/0.61      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.38/0.61         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['0', '1'])).
% 0.38/0.61  thf(t21_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.38/0.61  thf('3', plain,
% 0.38/0.61      (![X2 : $i, X3 : $i]:
% 0.38/0.61         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (X2))),
% 0.38/0.61      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.38/0.61  thf('4', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.61           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.61  thf('5', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.38/0.61           = (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['3', '4'])).
% 0.38/0.61  thf(t46_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.38/0.61  thf('6', plain,
% 0.38/0.61      (![X4 : $i, X5 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (k1_xboole_0))),
% 0.38/0.61      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.38/0.61  thf('7', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['5', '6'])).
% 0.38/0.61  thf('8', plain,
% 0.38/0.61      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.38/0.61      inference('demod', [status(thm)], ['2', '7'])).
% 0.38/0.61  thf(t98_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.38/0.61  thf('9', plain,
% 0.38/0.61      (![X7 : $i, X8 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X7 @ X8)
% 0.38/0.61           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.38/0.61  thf('10', plain,
% 0.38/0.61      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.38/0.61         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['8', '9'])).
% 0.38/0.61  thf(t5_boole, axiom,
% 0.38/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.61  thf('11', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.38/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.61  thf('12', plain,
% 0.38/0.61      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.38/0.61         = (k1_tarski @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.38/0.61  thf(t69_enumset1, axiom,
% 0.38/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.61  thf('13', plain,
% 0.38/0.61      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.38/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.61  thf(t70_enumset1, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.38/0.61  thf('14', plain,
% 0.38/0.61      (![X33 : $i, X34 : $i]:
% 0.38/0.61         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 0.38/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.61  thf(t46_enumset1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.61     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.38/0.61       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.38/0.61  thf('15', plain,
% 0.38/0.61      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.61         ((k2_enumset1 @ X28 @ X29 @ X30 @ X31)
% 0.38/0.61           = (k2_xboole_0 @ (k1_enumset1 @ X28 @ X29 @ X30) @ (k1_tarski @ X31)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.38/0.61  thf('16', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.61         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.38/0.61           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['14', '15'])).
% 0.38/0.61  thf('17', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.38/0.61           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['13', '16'])).
% 0.38/0.61  thf(t71_enumset1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.38/0.61  thf('18', plain,
% 0.38/0.61      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.38/0.61         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 0.38/0.61           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 0.38/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.38/0.61  thf('19', plain,
% 0.38/0.61      (![X33 : $i, X34 : $i]:
% 0.38/0.61         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 0.38/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.61  thf('20', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['18', '19'])).
% 0.38/0.61  thf(t72_enumset1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.61     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.38/0.61  thf('21', plain,
% 0.38/0.61      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.38/0.61         ((k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41)
% 0.38/0.61           = (k2_enumset1 @ X38 @ X39 @ X40 @ X41))),
% 0.38/0.61      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.38/0.61  thf('22', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['20', '21'])).
% 0.38/0.61  thf(commutativity_k2_tarski, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.38/0.61  thf('23', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.38/0.61  thf('24', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_tarski @ X0 @ X1) = (k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['22', '23'])).
% 0.38/0.61  thf('25', plain,
% 0.38/0.61      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.38/0.61         ((k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41)
% 0.38/0.61           = (k2_enumset1 @ X38 @ X39 @ X40 @ X41))),
% 0.38/0.61      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.38/0.61  thf('26', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_tarski @ X1 @ X0) = (k2_enumset1 @ X0 @ X0 @ X0 @ X1))),
% 0.38/0.61      inference('sup+', [status(thm)], ['24', '25'])).
% 0.38/0.61  thf('27', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_tarski @ X1 @ X0)
% 0.38/0.61           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.38/0.61      inference('demod', [status(thm)], ['17', '26'])).
% 0.38/0.61  thf('28', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.38/0.61  thf('29', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['12', '27', '28'])).
% 0.38/0.61  thf('30', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.61         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.38/0.61           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['14', '15'])).
% 0.38/0.61  thf('31', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((k2_enumset1 @ sk_B @ sk_B @ sk_A @ X0)
% 0.38/0.61           = (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ X0)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['29', '30'])).
% 0.38/0.61  thf('32', plain,
% 0.38/0.61      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.38/0.61         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 0.38/0.61           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 0.38/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.38/0.61  thf('33', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_tarski @ X1 @ X0)
% 0.38/0.61           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.38/0.61      inference('demod', [status(thm)], ['17', '26'])).
% 0.38/0.61  thf('34', plain,
% 0.38/0.61      (![X0 : $i]: ((k1_enumset1 @ sk_B @ sk_A @ X0) = (k2_tarski @ X0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.38/0.61  thf(d1_enumset1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.38/0.61       ( ![E:$i]:
% 0.38/0.61         ( ( r2_hidden @ E @ D ) <=>
% 0.38/0.61           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.38/0.61  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.38/0.61  thf(zf_stmt_2, axiom,
% 0.38/0.61    (![E:$i,C:$i,B:$i,A:$i]:
% 0.38/0.61     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.38/0.61       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.38/0.61  thf(zf_stmt_3, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.38/0.61       ( ![E:$i]:
% 0.38/0.61         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.38/0.61  thf('35', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.61         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.38/0.61          | (r2_hidden @ X16 @ X20)
% 0.38/0.61          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.61  thf('36', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.61         ((r2_hidden @ X16 @ (k1_enumset1 @ X19 @ X18 @ X17))
% 0.38/0.61          | (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19))),
% 0.38/0.61      inference('simplify', [status(thm)], ['35'])).
% 0.38/0.61  thf('37', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((r2_hidden @ X1 @ (k2_tarski @ X0 @ sk_B))
% 0.38/0.61          | (zip_tseitin_0 @ X1 @ X0 @ sk_A @ sk_B))),
% 0.38/0.61      inference('sup+', [status(thm)], ['34', '36'])).
% 0.38/0.61  thf('38', plain,
% 0.38/0.61      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.61         (((X12) != (X14)) | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X11))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.61  thf('39', plain,
% 0.38/0.61      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.38/0.61         ~ (zip_tseitin_0 @ X14 @ X13 @ X14 @ X11)),
% 0.38/0.61      inference('simplify', [status(thm)], ['38'])).
% 0.38/0.61  thf('40', plain, (![X0 : $i]: (r2_hidden @ sk_A @ (k2_tarski @ X0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['37', '39'])).
% 0.38/0.61  thf('41', plain,
% 0.38/0.61      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.38/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.61  thf(d1_tarski, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.38/0.61  thf('42', plain,
% 0.38/0.61      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.38/0.61         (~ (r2_hidden @ X26 @ X25)
% 0.38/0.61          | ((X26) = (X23))
% 0.38/0.61          | ((X25) != (k1_tarski @ X23)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.61  thf('43', plain,
% 0.38/0.61      (![X23 : $i, X26 : $i]:
% 0.38/0.61         (((X26) = (X23)) | ~ (r2_hidden @ X26 @ (k1_tarski @ X23)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['42'])).
% 0.38/0.61  thf('44', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)) | ((X1) = (X0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['41', '43'])).
% 0.38/0.61  thf('45', plain, (((sk_A) = (sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['40', '44'])).
% 0.38/0.61  thf('46', plain, (((sk_A) != (sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('47', plain, ($false),
% 0.38/0.61      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.38/0.61  
% 0.38/0.61  % SZS output end Refutation
% 0.38/0.61  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

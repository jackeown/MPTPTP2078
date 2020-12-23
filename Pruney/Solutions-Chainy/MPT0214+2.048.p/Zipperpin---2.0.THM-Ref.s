%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.15KjBQQp2A

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:50 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 141 expanded)
%              Number of leaves         :   29 (  56 expanded)
%              Depth                    :   17
%              Number of atoms          :  575 (1099 expanded)
%              Number of equality atoms :   65 ( 125 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('9',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('11',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('14',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X23 @ X24 @ X25 ) @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('17',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k2_enumset1 @ X30 @ X30 @ X31 @ X32 )
      = ( k1_enumset1 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('18',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ sk_B @ sk_B @ sk_A @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k2_enumset1 @ X30 @ X30 @ X31 @ X32 )
      = ( k1_enumset1 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X22 @ X21 @ X20 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ sk_A @ sk_B )
      = ( k2_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['23','26','27'])).

thf('29',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('30',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['11','20'])).

thf('32',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
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

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X8 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('42',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('43',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','47'])).

thf('49',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('51',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.15KjBQQp2A
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 193 iterations in 0.066s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.19/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.19/0.52  thf(d1_enumset1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.52     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.19/0.52       ( ![E:$i]:
% 0.19/0.52         ( ( r2_hidden @ E @ D ) <=>
% 0.19/0.52           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_0, axiom,
% 0.19/0.52    (![E:$i,C:$i,B:$i,A:$i]:
% 0.19/0.52     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.19/0.52       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.19/0.52  thf('0', plain,
% 0.19/0.52      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.52         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.19/0.52          | ((X9) = (X10))
% 0.19/0.52          | ((X9) = (X11))
% 0.19/0.52          | ((X9) = (X12)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(t6_zfmisc_1, conjecture,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.19/0.52       ( ( A ) = ( B ) ) ))).
% 0.19/0.52  thf(zf_stmt_1, negated_conjecture,
% 0.19/0.52    (~( ![A:$i,B:$i]:
% 0.19/0.52        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.19/0.52          ( ( A ) = ( B ) ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.19/0.52  thf('1', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.53  thf(t28_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      (![X2 : $i, X3 : $i]:
% 0.19/0.53         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.19/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.53  thf('3', plain,
% 0.19/0.53      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.53         = (k1_tarski @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.53  thf(t100_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.53  thf('4', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k4_xboole_0 @ X0 @ X1)
% 0.19/0.53           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.53         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.19/0.53  thf(t92_xboole_1, axiom,
% 0.19/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.53  thf('6', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.19/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.19/0.53  thf(t98_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.19/0.53  thf('8', plain,
% 0.19/0.53      (![X6 : $i, X7 : $i]:
% 0.19/0.53         ((k2_xboole_0 @ X6 @ X7)
% 0.19/0.53           = (k5_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.19/0.53         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.53  thf(t5_boole, axiom,
% 0.19/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.53  thf('10', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.19/0.53      inference('cnf', [status(esa)], [t5_boole])).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.19/0.53         = (k1_tarski @ sk_B))),
% 0.19/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.53  thf(t69_enumset1, axiom,
% 0.19/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.53  thf('12', plain,
% 0.19/0.53      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.19/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.53  thf(t70_enumset1, axiom,
% 0.19/0.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      (![X28 : $i, X29 : $i]:
% 0.19/0.53         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.19/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.53  thf(t46_enumset1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.53     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.19/0.53       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.19/0.53         ((k2_enumset1 @ X23 @ X24 @ X25 @ X26)
% 0.19/0.53           = (k2_xboole_0 @ (k1_enumset1 @ X23 @ X24 @ X25) @ (k1_tarski @ X26)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.19/0.53           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.19/0.53           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['12', '15'])).
% 0.19/0.53  thf(t71_enumset1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.53         ((k2_enumset1 @ X30 @ X30 @ X31 @ X32)
% 0.19/0.53           = (k1_enumset1 @ X30 @ X31 @ X32))),
% 0.19/0.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.19/0.53  thf('18', plain,
% 0.19/0.53      (![X28 : $i, X29 : $i]:
% 0.19/0.53         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.19/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.53  thf('19', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['17', '18'])).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k2_tarski @ X0 @ X1)
% 0.19/0.53           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.19/0.53      inference('demod', [status(thm)], ['16', '19'])).
% 0.19/0.53  thf('21', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.19/0.53      inference('demod', [status(thm)], ['11', '20'])).
% 0.19/0.53  thf('22', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.19/0.53           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.53  thf('23', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k2_enumset1 @ sk_B @ sk_B @ sk_A @ X0)
% 0.19/0.53           = (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ X0)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['21', '22'])).
% 0.19/0.53  thf('24', plain,
% 0.19/0.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.53         ((k2_enumset1 @ X30 @ X30 @ X31 @ X32)
% 0.19/0.53           = (k1_enumset1 @ X30 @ X31 @ X32))),
% 0.19/0.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.19/0.53  thf(t102_enumset1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.19/0.53  thf('25', plain,
% 0.19/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.53         ((k1_enumset1 @ X22 @ X21 @ X20) = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.19/0.53      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.19/0.53  thf('26', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['24', '25'])).
% 0.19/0.53  thf('27', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k2_tarski @ X0 @ X1)
% 0.19/0.53           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.19/0.53      inference('demod', [status(thm)], ['16', '19'])).
% 0.19/0.53  thf('28', plain,
% 0.19/0.53      (![X0 : $i]: ((k1_enumset1 @ X0 @ sk_A @ sk_B) = (k2_tarski @ sk_B @ X0))),
% 0.19/0.53      inference('demod', [status(thm)], ['23', '26', '27'])).
% 0.19/0.53  thf('29', plain,
% 0.19/0.53      (![X28 : $i, X29 : $i]:
% 0.19/0.53         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.19/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.53  thf('30', plain, (((k2_tarski @ sk_B @ sk_A) = (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.53      inference('sup+', [status(thm)], ['28', '29'])).
% 0.19/0.53  thf('31', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.19/0.53      inference('demod', [status(thm)], ['11', '20'])).
% 0.19/0.53  thf('32', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.19/0.53      inference('sup+', [status(thm)], ['30', '31'])).
% 0.19/0.53  thf('33', plain,
% 0.19/0.53      (![X28 : $i, X29 : $i]:
% 0.19/0.53         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.19/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.53  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.19/0.53  thf(zf_stmt_3, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.53     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.19/0.53       ( ![E:$i]:
% 0.19/0.53         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.19/0.53  thf('34', plain,
% 0.19/0.53      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.53         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.19/0.53          | (r2_hidden @ X13 @ X17)
% 0.19/0.53          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.53  thf('35', plain,
% 0.19/0.53      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.53         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 0.19/0.53          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.19/0.53      inference('simplify', [status(thm)], ['34'])).
% 0.19/0.53  thf('36', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.19/0.53          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.19/0.53      inference('sup+', [status(thm)], ['33', '35'])).
% 0.19/0.53  thf('37', plain,
% 0.19/0.53      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.53         (((X9) != (X8)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('38', plain,
% 0.19/0.53      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X8 @ X10 @ X11 @ X8)),
% 0.19/0.53      inference('simplify', [status(thm)], ['37'])).
% 0.19/0.53  thf('39', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['36', '38'])).
% 0.19/0.53  thf('40', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.19/0.53      inference('sup+', [status(thm)], ['32', '39'])).
% 0.19/0.53  thf('41', plain,
% 0.19/0.53      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.19/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.53  thf('42', plain,
% 0.19/0.53      (![X28 : $i, X29 : $i]:
% 0.19/0.53         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.19/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.53  thf('43', plain,
% 0.19/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X18 @ X17)
% 0.19/0.53          | ~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.19/0.53          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.53  thf('44', plain,
% 0.19/0.53      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.19/0.53         (~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.19/0.53          | ~ (r2_hidden @ X18 @ (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['43'])).
% 0.19/0.53  thf('45', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.19/0.53          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['42', '44'])).
% 0.19/0.53  thf('46', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.19/0.53          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['41', '45'])).
% 0.19/0.53  thf('47', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.19/0.53      inference('sup-', [status(thm)], ['40', '46'])).
% 0.19/0.53  thf('48', plain,
% 0.19/0.53      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['0', '47'])).
% 0.19/0.53  thf('49', plain, (((sk_A) = (sk_B))),
% 0.19/0.53      inference('simplify', [status(thm)], ['48'])).
% 0.19/0.53  thf('50', plain, (((sk_A) != (sk_B))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.53  thf('51', plain, ($false),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.34/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

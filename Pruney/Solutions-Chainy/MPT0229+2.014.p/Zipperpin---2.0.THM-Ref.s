%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sulSN3g1f6

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 (  90 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  529 ( 622 expanded)
%              Number of equality atoms :   62 (  75 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

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
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( X12 = X13 )
      | ( X12 = X14 )
      | ( X12 = X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t24_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
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

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','14'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('17',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('19',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('22',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X23 @ X24 @ X25 ) @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('25',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k2_enumset1 @ X30 @ X30 @ X31 @ X32 )
      = ( k1_enumset1 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('26',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X20 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X13 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ~ ( zip_tseitin_0 @ X13 @ X13 @ X14 @ X11 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('39',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('40',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X17 @ X18 @ X19 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X17 @ X18 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','44'])).

thf('46',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sulSN3g1f6
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:12:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 138 iterations in 0.065s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.22/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.53  thf(d1_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.53       ( ![E:$i]:
% 0.22/0.53         ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.53           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, axiom,
% 0.22/0.53    (![E:$i,C:$i,B:$i,A:$i]:
% 0.22/0.53     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.22/0.53       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.53         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 0.22/0.53          | ((X12) = (X13))
% 0.22/0.53          | ((X12) = (X14))
% 0.22/0.53          | ((X12) = (X15)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t24_zfmisc_1, conjecture,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.22/0.53       ( ( A ) = ( B ) ) ))).
% 0.22/0.53  thf(zf_stmt_1, negated_conjecture,
% 0.22/0.53    (~( ![A:$i,B:$i]:
% 0.22/0.53        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.22/0.53          ( ( A ) = ( B ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t24_zfmisc_1])).
% 0.22/0.53  thf('1', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.53  thf(t28_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X5 : $i, X6 : $i]:
% 0.22/0.53         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.22/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.53         = (k1_tarski @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf(t100_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.53           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.53         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.53  thf(t1_boole, axiom,
% 0.22/0.53    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.53  thf('6', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.22/0.53      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.53  thf(t21_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (![X3 : $i, X4 : $i]:
% 0.22/0.53         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (X3))),
% 0.22/0.53      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.22/0.53  thf('8', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.53           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.53  thf('11', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.22/0.53      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.53  thf(t46_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (![X9 : $i, X10 : $i]:
% 0.22/0.53         ((k4_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.22/0.53  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.53  thf('14', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['10', '13'])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.22/0.53      inference('demod', [status(thm)], ['5', '14'])).
% 0.22/0.53  thf(t39_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      (![X7 : $i, X8 : $i]:
% 0.22/0.53         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.22/0.53           = (k2_xboole_0 @ X7 @ X8))),
% 0.22/0.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.22/0.53         = (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['15', '16'])).
% 0.22/0.53  thf('18', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.22/0.53      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.53  thf('19', plain,
% 0.22/0.53      (((k1_tarski @ sk_B)
% 0.22/0.53         = (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.22/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.53  thf(t69_enumset1, axiom,
% 0.22/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.22/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.53  thf(t70_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      (![X28 : $i, X29 : $i]:
% 0.22/0.53         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.22/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.53  thf(t46_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.22/0.53       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.53         ((k2_enumset1 @ X23 @ X24 @ X25 @ X26)
% 0.22/0.53           = (k2_xboole_0 @ (k1_enumset1 @ X23 @ X24 @ X25) @ (k1_tarski @ X26)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.22/0.53           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['21', '22'])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.22/0.53           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['20', '23'])).
% 0.22/0.53  thf(t71_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.22/0.53         ((k2_enumset1 @ X30 @ X30 @ X31 @ X32)
% 0.22/0.53           = (k1_enumset1 @ X30 @ X31 @ X32))),
% 0.22/0.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      (![X28 : $i, X29 : $i]:
% 0.22/0.53         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.22/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.53  thf('27', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['25', '26'])).
% 0.22/0.53  thf('28', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k2_tarski @ X0 @ X1)
% 0.22/0.53           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.22/0.53      inference('demod', [status(thm)], ['24', '27'])).
% 0.22/0.53  thf('29', plain, (((k1_tarski @ sk_B) = (k2_tarski @ sk_B @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['19', '28'])).
% 0.22/0.53  thf('30', plain,
% 0.22/0.53      (![X28 : $i, X29 : $i]:
% 0.22/0.53         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.22/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.53  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.53  thf(zf_stmt_3, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.53       ( ![E:$i]:
% 0.22/0.53         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.53         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.22/0.53          | (r2_hidden @ X16 @ X20)
% 0.22/0.53          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.53         ((r2_hidden @ X16 @ (k1_enumset1 @ X19 @ X18 @ X17))
% 0.22/0.53          | (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19))),
% 0.22/0.53      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.53  thf('33', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.53          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.53      inference('sup+', [status(thm)], ['30', '32'])).
% 0.22/0.53  thf('34', plain,
% 0.22/0.53      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.53         (((X12) != (X13)) | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X11))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('35', plain,
% 0.22/0.53      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.22/0.53         ~ (zip_tseitin_0 @ X13 @ X13 @ X14 @ X11)),
% 0.22/0.53      inference('simplify', [status(thm)], ['34'])).
% 0.22/0.53  thf('36', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['33', '35'])).
% 0.22/0.53  thf('37', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.22/0.53      inference('sup+', [status(thm)], ['29', '36'])).
% 0.22/0.53  thf('38', plain,
% 0.22/0.53      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.22/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.53  thf('39', plain,
% 0.22/0.53      (![X28 : $i, X29 : $i]:
% 0.22/0.53         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.22/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.53  thf('40', plain,
% 0.22/0.53      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X21 @ X20)
% 0.22/0.53          | ~ (zip_tseitin_0 @ X21 @ X17 @ X18 @ X19)
% 0.22/0.53          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.53  thf('41', plain,
% 0.22/0.53      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.22/0.53         (~ (zip_tseitin_0 @ X21 @ X17 @ X18 @ X19)
% 0.22/0.53          | ~ (r2_hidden @ X21 @ (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['40'])).
% 0.22/0.53  thf('42', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.53          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['39', '41'])).
% 0.22/0.53  thf('43', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.22/0.53          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['38', '42'])).
% 0.22/0.53  thf('44', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.22/0.53      inference('sup-', [status(thm)], ['37', '43'])).
% 0.22/0.53  thf('45', plain,
% 0.22/0.53      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['0', '44'])).
% 0.22/0.53  thf('46', plain, (((sk_A) = (sk_B))),
% 0.22/0.53      inference('simplify', [status(thm)], ['45'])).
% 0.22/0.53  thf('47', plain, (((sk_A) != (sk_B))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.53  thf('48', plain, ($false),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

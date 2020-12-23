%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xZnMdJJRiD

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 (  99 expanded)
%              Number of leaves         :   30 (  42 expanded)
%              Depth                    :   16
%              Number of atoms          :  536 ( 692 expanded)
%              Number of equality atoms :   66 (  88 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( X18 = X19 )
      | ( X18 = X20 )
      | ( X18 = X21 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','14','19'])).

thf('21',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','20'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('23',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_tarski @ X29 ) @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('27',plain,
    ( ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['27','32'])).

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
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 )
      | ( r2_hidden @ X22 @ X26 )
      | ( X26
       != ( k1_enumset1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X22 @ ( k1_enumset1 @ X25 @ X24 @ X23 ) )
      | ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X18 != X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ~ ( zip_tseitin_0 @ X17 @ X19 @ X20 @ X17 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('41',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ~ ( zip_tseitin_0 @ X27 @ X23 @ X24 @ X25 )
      | ( X26
       != ( k1_enumset1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('42',plain,(
    ! [X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X23 @ X24 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k1_enumset1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['0','44'])).

thf('46',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xZnMdJJRiD
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:16:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 96 iterations in 0.043s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(d1_enumset1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.50       ( ![E:$i]:
% 0.20/0.50         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.50           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, axiom,
% 0.20/0.50    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.50     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.50       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.50         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 0.20/0.50          | ((X18) = (X19))
% 0.20/0.50          | ((X18) = (X20))
% 0.20/0.50          | ((X18) = (X21)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t25_zfmisc_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.20/0.50          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_1, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.50        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.20/0.50             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.50  thf(t28_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.20/0.50         = (k1_tarski @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf(t100_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X7 @ X8)
% 0.20/0.50           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.20/0.50         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf(t3_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.50  thf('6', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.50  thf(t48_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.20/0.50           = (k3_xboole_0 @ X13 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('10', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.20/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.50  thf('12', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X7 @ X8)
% 0.20/0.50           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.50  thf('15', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['8', '14', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.20/0.50         = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['5', '20'])).
% 0.20/0.50  thf(t98_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i]:
% 0.20/0.50         ((k2_xboole_0 @ X15 @ X16)
% 0.20/0.50           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.20/0.50         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.20/0.50         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.50  thf(t42_enumset1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.50       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.50         ((k1_enumset1 @ X29 @ X30 @ X31)
% 0.20/0.50           = (k2_xboole_0 @ (k1_tarski @ X29) @ (k2_tarski @ X30 @ X31)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.20/0.50         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X7 @ X8)
% 0.20/0.50           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf('31', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.50  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (((k1_enumset1 @ sk_A @ sk_B @ sk_C) = (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['27', '32'])).
% 0.20/0.50  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_3, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.50       ( ![E:$i]:
% 0.20/0.50         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.50         ((zip_tseitin_0 @ X22 @ X23 @ X24 @ X25)
% 0.20/0.50          | (r2_hidden @ X22 @ X26)
% 0.20/0.50          | ((X26) != (k1_enumset1 @ X25 @ X24 @ X23)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.50         ((r2_hidden @ X22 @ (k1_enumset1 @ X25 @ X24 @ X23))
% 0.20/0.50          | (zip_tseitin_0 @ X22 @ X23 @ X24 @ X25))),
% 0.20/0.50      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 0.20/0.50          | (zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['33', '35'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.50         (((X18) != (X17)) | ~ (zip_tseitin_0 @ X18 @ X19 @ X20 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.20/0.50         ~ (zip_tseitin_0 @ X17 @ X19 @ X20 @ X17)),
% 0.20/0.50      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.50  thf('39', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['36', '38'])).
% 0.20/0.50  thf(t70_enumset1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X33 : $i, X34 : $i]:
% 0.20/0.50         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 0.20/0.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X27 @ X26)
% 0.20/0.50          | ~ (zip_tseitin_0 @ X27 @ X23 @ X24 @ X25)
% 0.20/0.50          | ((X26) != (k1_enumset1 @ X25 @ X24 @ X23)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X23 : $i, X24 : $i, X25 : $i, X27 : $i]:
% 0.20/0.50         (~ (zip_tseitin_0 @ X27 @ X23 @ X24 @ X25)
% 0.20/0.50          | ~ (r2_hidden @ X27 @ (k1_enumset1 @ X25 @ X24 @ X23)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.50          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '42'])).
% 0.20/0.50  thf('44', plain, (~ (zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['39', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '44'])).
% 0.20/0.50  thf('46', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.50  thf('47', plain, (((sk_A) != (sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.50  thf('48', plain, (((sk_A) != (sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.50  thf('49', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['46', '47', '48'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

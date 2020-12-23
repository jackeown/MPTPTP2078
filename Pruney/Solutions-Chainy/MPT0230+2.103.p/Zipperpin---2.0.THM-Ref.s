%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vo1cvTb3H6

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:22 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   76 (  83 expanded)
%              Number of leaves         :   34 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  560 ( 633 expanded)
%              Number of equality atoms :   68 (  79 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X38: $i] :
      ( ( k2_tarski @ X38 @ X38 )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X69: $i,X70: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X69 ) @ ( k2_tarski @ X69 @ X70 ) )
      = ( k1_tarski @ X69 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X38: $i] :
      ( ( k2_tarski @ X38 @ X38 )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X71: $i,X72: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X71 ) @ ( k2_tarski @ X71 @ X72 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t22_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('17',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['6','15','16'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('18',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( k2_enumset1 @ X41 @ X41 @ X42 @ X43 )
      = ( k1_enumset1 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_enumset1 @ X39 @ X39 @ X40 )
      = ( k2_tarski @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('21',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X33 @ X34 @ X35 @ X36 ) @ ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('23',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k3_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 )
      = ( k2_enumset1 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('24',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( k2_enumset1 @ X41 @ X41 @ X42 @ X43 )
      = ( k1_enumset1 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('27',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( k1_enumset1 @ X66 @ X68 @ X67 )
      = ( k1_enumset1 @ X66 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('28',plain,
    ( ( k1_enumset1 @ sk_B @ sk_A @ sk_C )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['17','26','27'])).

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

thf('29',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( r2_hidden @ X12 @ X16 )
      | ( X16
       != ( k1_enumset1 @ X15 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ ( k1_enumset1 @ X15 @ X14 @ X13 ) )
      | ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['28','30'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('32',plain,(
    ! [X19: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X21 )
      | ( X23 = X22 )
      | ( X23 = X19 )
      | ( X21
       != ( k2_tarski @ X22 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('33',plain,(
    ! [X19: $i,X22: $i,X23: $i] :
      ( ( X23 = X19 )
      | ( X23 = X22 )
      | ~ ( r2_hidden @ X23 @ ( k2_tarski @ X22 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_C @ sk_A @ sk_B )
      | ( X0 = sk_B )
      | ( X0 = sk_C ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X10 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ~ ( zip_tseitin_0 @ X10 @ X9 @ X10 @ X7 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vo1cvTb3H6
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:03:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.83/1.02  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.83/1.02  % Solved by: fo/fo7.sh
% 0.83/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.02  % done 1182 iterations in 0.571s
% 0.83/1.02  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.83/1.02  % SZS output start Refutation
% 0.83/1.02  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.83/1.02  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.83/1.02  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.02  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.83/1.02  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.83/1.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.83/1.02  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.83/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.02  thf(sk_C_type, type, sk_C: $i).
% 0.83/1.02  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.83/1.02  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.83/1.02  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.83/1.02  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.83/1.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.83/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.02  thf(t25_zfmisc_1, conjecture,
% 0.83/1.02    (![A:$i,B:$i,C:$i]:
% 0.83/1.02     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.83/1.02          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.83/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.02    (~( ![A:$i,B:$i,C:$i]:
% 0.83/1.02        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.83/1.02             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.83/1.02    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.83/1.02  thf('0', plain,
% 0.83/1.02      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.83/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.02  thf(t28_xboole_1, axiom,
% 0.83/1.02    (![A:$i,B:$i]:
% 0.83/1.02     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.83/1.02  thf('1', plain,
% 0.83/1.02      (![X2 : $i, X3 : $i]:
% 0.83/1.02         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.83/1.02      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.83/1.02  thf('2', plain,
% 0.83/1.02      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.83/1.02         = (k1_tarski @ sk_A))),
% 0.83/1.02      inference('sup-', [status(thm)], ['0', '1'])).
% 0.83/1.02  thf(t100_xboole_1, axiom,
% 0.83/1.02    (![A:$i,B:$i]:
% 0.83/1.02     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.83/1.02  thf('3', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k4_xboole_0 @ X0 @ X1)
% 0.83/1.02           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.83/1.02      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.83/1.02  thf('4', plain,
% 0.83/1.02      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.83/1.02         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.83/1.02      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.02  thf(t98_xboole_1, axiom,
% 0.83/1.02    (![A:$i,B:$i]:
% 0.83/1.02     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.83/1.02  thf('5', plain,
% 0.83/1.02      (![X5 : $i, X6 : $i]:
% 0.83/1.02         ((k2_xboole_0 @ X5 @ X6)
% 0.83/1.02           = (k5_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5)))),
% 0.83/1.02      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.83/1.02  thf('6', plain,
% 0.83/1.02      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.83/1.02         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ 
% 0.83/1.02            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.83/1.02      inference('sup+', [status(thm)], ['4', '5'])).
% 0.83/1.02  thf(t69_enumset1, axiom,
% 0.83/1.02    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.83/1.02  thf('7', plain, (![X38 : $i]: ((k2_tarski @ X38 @ X38) = (k1_tarski @ X38))),
% 0.83/1.02      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.83/1.02  thf(t19_zfmisc_1, axiom,
% 0.83/1.02    (![A:$i,B:$i]:
% 0.83/1.02     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.83/1.02       ( k1_tarski @ A ) ))).
% 0.83/1.02  thf('8', plain,
% 0.83/1.02      (![X69 : $i, X70 : $i]:
% 0.83/1.02         ((k3_xboole_0 @ (k1_tarski @ X69) @ (k2_tarski @ X69 @ X70))
% 0.83/1.02           = (k1_tarski @ X69))),
% 0.83/1.02      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.83/1.02  thf('9', plain,
% 0.83/1.02      (![X0 : $i]:
% 0.83/1.02         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.83/1.02           = (k1_tarski @ X0))),
% 0.83/1.02      inference('sup+', [status(thm)], ['7', '8'])).
% 0.83/1.02  thf('10', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k4_xboole_0 @ X0 @ X1)
% 0.83/1.02           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.83/1.02      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.83/1.02  thf('11', plain,
% 0.83/1.02      (![X0 : $i]:
% 0.83/1.02         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.83/1.02           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.83/1.02      inference('sup+', [status(thm)], ['9', '10'])).
% 0.83/1.02  thf('12', plain,
% 0.83/1.02      (![X38 : $i]: ((k2_tarski @ X38 @ X38) = (k1_tarski @ X38))),
% 0.83/1.02      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.83/1.02  thf(t22_zfmisc_1, axiom,
% 0.83/1.02    (![A:$i,B:$i]:
% 0.83/1.02     ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.83/1.02       ( k1_xboole_0 ) ))).
% 0.83/1.02  thf('13', plain,
% 0.83/1.02      (![X71 : $i, X72 : $i]:
% 0.83/1.02         ((k4_xboole_0 @ (k1_tarski @ X71) @ (k2_tarski @ X71 @ X72))
% 0.83/1.02           = (k1_xboole_0))),
% 0.83/1.02      inference('cnf', [status(esa)], [t22_zfmisc_1])).
% 0.83/1.02  thf('14', plain,
% 0.83/1.02      (![X0 : $i]:
% 0.83/1.02         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.83/1.02      inference('sup+', [status(thm)], ['12', '13'])).
% 0.83/1.02  thf('15', plain,
% 0.83/1.02      (![X0 : $i]:
% 0.83/1.02         ((k1_xboole_0) = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.83/1.02      inference('demod', [status(thm)], ['11', '14'])).
% 0.83/1.02  thf(t5_boole, axiom,
% 0.83/1.02    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.83/1.02  thf('16', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.83/1.02      inference('cnf', [status(esa)], [t5_boole])).
% 0.83/1.02  thf('17', plain,
% 0.83/1.02      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.83/1.02         = (k2_tarski @ sk_B @ sk_C))),
% 0.83/1.02      inference('demod', [status(thm)], ['6', '15', '16'])).
% 0.83/1.02  thf(t71_enumset1, axiom,
% 0.83/1.02    (![A:$i,B:$i,C:$i]:
% 0.83/1.02     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.83/1.02  thf('18', plain,
% 0.83/1.02      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.83/1.02         ((k2_enumset1 @ X41 @ X41 @ X42 @ X43)
% 0.83/1.02           = (k1_enumset1 @ X41 @ X42 @ X43))),
% 0.83/1.02      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.83/1.02  thf(t70_enumset1, axiom,
% 0.83/1.02    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.83/1.02  thf('19', plain,
% 0.83/1.02      (![X39 : $i, X40 : $i]:
% 0.83/1.02         ((k1_enumset1 @ X39 @ X39 @ X40) = (k2_tarski @ X39 @ X40))),
% 0.83/1.02      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.83/1.02  thf('20', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.83/1.02      inference('sup+', [status(thm)], ['18', '19'])).
% 0.83/1.02  thf(t50_enumset1, axiom,
% 0.83/1.02    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.83/1.02     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.83/1.02       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.83/1.02  thf('21', plain,
% 0.83/1.02      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.83/1.02         ((k3_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37)
% 0.83/1.02           = (k2_xboole_0 @ (k2_enumset1 @ X33 @ X34 @ X35 @ X36) @ 
% 0.83/1.02              (k1_tarski @ X37)))),
% 0.83/1.02      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.83/1.02  thf('22', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.02         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 0.83/1.02           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.83/1.02      inference('sup+', [status(thm)], ['20', '21'])).
% 0.83/1.02  thf(t72_enumset1, axiom,
% 0.83/1.02    (![A:$i,B:$i,C:$i,D:$i]:
% 0.83/1.02     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.83/1.02  thf('23', plain,
% 0.83/1.02      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.83/1.02         ((k3_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47)
% 0.83/1.02           = (k2_enumset1 @ X44 @ X45 @ X46 @ X47))),
% 0.83/1.02      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.83/1.02  thf('24', plain,
% 0.83/1.02      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.83/1.02         ((k2_enumset1 @ X41 @ X41 @ X42 @ X43)
% 0.83/1.02           = (k1_enumset1 @ X41 @ X42 @ X43))),
% 0.83/1.02      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.83/1.02  thf('25', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.02         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.83/1.02      inference('sup+', [status(thm)], ['23', '24'])).
% 0.83/1.02  thf('26', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.02         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.83/1.02           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.83/1.02      inference('sup+', [status(thm)], ['22', '25'])).
% 0.83/1.02  thf(t98_enumset1, axiom,
% 0.83/1.02    (![A:$i,B:$i,C:$i]:
% 0.83/1.02     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.83/1.02  thf('27', plain,
% 0.83/1.02      (![X66 : $i, X67 : $i, X68 : $i]:
% 0.83/1.02         ((k1_enumset1 @ X66 @ X68 @ X67) = (k1_enumset1 @ X66 @ X67 @ X68))),
% 0.83/1.02      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.83/1.02  thf('28', plain,
% 0.83/1.02      (((k1_enumset1 @ sk_B @ sk_A @ sk_C) = (k2_tarski @ sk_B @ sk_C))),
% 0.83/1.02      inference('demod', [status(thm)], ['17', '26', '27'])).
% 0.83/1.02  thf(d1_enumset1, axiom,
% 0.83/1.02    (![A:$i,B:$i,C:$i,D:$i]:
% 0.83/1.02     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.83/1.02       ( ![E:$i]:
% 0.83/1.02         ( ( r2_hidden @ E @ D ) <=>
% 0.83/1.02           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.83/1.02  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.83/1.02  thf(zf_stmt_2, axiom,
% 0.83/1.02    (![E:$i,C:$i,B:$i,A:$i]:
% 0.83/1.02     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.83/1.02       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.83/1.02  thf(zf_stmt_3, axiom,
% 0.83/1.02    (![A:$i,B:$i,C:$i,D:$i]:
% 0.83/1.02     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.83/1.02       ( ![E:$i]:
% 0.83/1.02         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.83/1.02  thf('29', plain,
% 0.83/1.02      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.83/1.02         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 0.83/1.02          | (r2_hidden @ X12 @ X16)
% 0.83/1.02          | ((X16) != (k1_enumset1 @ X15 @ X14 @ X13)))),
% 0.83/1.02      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.83/1.02  thf('30', plain,
% 0.83/1.02      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.83/1.02         ((r2_hidden @ X12 @ (k1_enumset1 @ X15 @ X14 @ X13))
% 0.83/1.02          | (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 0.83/1.02      inference('simplify', [status(thm)], ['29'])).
% 0.83/1.02  thf('31', plain,
% 0.83/1.02      (![X0 : $i]:
% 0.83/1.02         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 0.83/1.02          | (zip_tseitin_0 @ X0 @ sk_C @ sk_A @ sk_B))),
% 0.83/1.02      inference('sup+', [status(thm)], ['28', '30'])).
% 0.83/1.02  thf(d2_tarski, axiom,
% 0.83/1.02    (![A:$i,B:$i,C:$i]:
% 0.83/1.02     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.83/1.02       ( ![D:$i]:
% 0.83/1.02         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.83/1.02  thf('32', plain,
% 0.83/1.02      (![X19 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.83/1.02         (~ (r2_hidden @ X23 @ X21)
% 0.83/1.02          | ((X23) = (X22))
% 0.83/1.02          | ((X23) = (X19))
% 0.83/1.02          | ((X21) != (k2_tarski @ X22 @ X19)))),
% 0.83/1.02      inference('cnf', [status(esa)], [d2_tarski])).
% 0.83/1.02  thf('33', plain,
% 0.83/1.02      (![X19 : $i, X22 : $i, X23 : $i]:
% 0.83/1.02         (((X23) = (X19))
% 0.83/1.02          | ((X23) = (X22))
% 0.83/1.02          | ~ (r2_hidden @ X23 @ (k2_tarski @ X22 @ X19)))),
% 0.83/1.02      inference('simplify', [status(thm)], ['32'])).
% 0.83/1.02  thf('34', plain,
% 0.83/1.02      (![X0 : $i]:
% 0.83/1.02         ((zip_tseitin_0 @ X0 @ sk_C @ sk_A @ sk_B)
% 0.83/1.02          | ((X0) = (sk_B))
% 0.83/1.02          | ((X0) = (sk_C)))),
% 0.83/1.02      inference('sup-', [status(thm)], ['31', '33'])).
% 0.83/1.02  thf('35', plain,
% 0.83/1.02      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.83/1.02         (((X8) != (X10)) | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X7))),
% 0.83/1.02      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.83/1.02  thf('36', plain,
% 0.83/1.02      (![X7 : $i, X9 : $i, X10 : $i]: ~ (zip_tseitin_0 @ X10 @ X9 @ X10 @ X7)),
% 0.83/1.02      inference('simplify', [status(thm)], ['35'])).
% 0.83/1.02  thf('37', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.83/1.02      inference('sup-', [status(thm)], ['34', '36'])).
% 0.83/1.02  thf('38', plain, (((sk_A) != (sk_B))),
% 0.83/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.02  thf('39', plain, (((sk_A) != (sk_C))),
% 0.83/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.02  thf('40', plain, ($false),
% 0.83/1.02      inference('simplify_reflect-', [status(thm)], ['37', '38', '39'])).
% 0.83/1.02  
% 0.83/1.02  % SZS output end Refutation
% 0.83/1.02  
% 0.83/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

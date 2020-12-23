%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8ifDxd1K6x

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:52 EST 2020

% Result     : Theorem 0.87s
% Output     : Refutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :   67 (  83 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  489 ( 630 expanded)
%              Number of equality atoms :   49 (  65 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X38: $i] :
      ( ( k2_tarski @ X38 @ X38 )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_enumset1 @ X39 @ X39 @ X40 )
      = ( k2_tarski @ X39 @ X40 ) ) ),
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

thf('5',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 )
      | ( r2_hidden @ X31 @ X35 )
      | ( X35
       != ( k1_enumset1 @ X34 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ X31 @ ( k1_enumset1 @ X34 @ X33 @ X32 ) )
      | ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X27 != X26 )
      | ~ ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ~ ( zip_tseitin_0 @ X26 @ X28 @ X29 @ X26 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['2','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('24',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X48 ) @ X49 )
      | ( r2_hidden @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t87_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ X23 @ X24 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X25 @ X23 ) @ X24 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X25 @ X24 ) @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) @ X0 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 )
        = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28','33'])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('39',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','18','19','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8ifDxd1K6x
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.87/1.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.87/1.08  % Solved by: fo/fo7.sh
% 0.87/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.87/1.08  % done 1179 iterations in 0.632s
% 0.87/1.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.87/1.08  % SZS output start Refutation
% 0.87/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.87/1.08  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.87/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.87/1.08  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.87/1.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.87/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.87/1.08  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.87/1.08  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.87/1.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.87/1.08  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.87/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.87/1.08  thf(t65_zfmisc_1, conjecture,
% 0.87/1.08    (![A:$i,B:$i]:
% 0.87/1.08     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.87/1.08       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.87/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.87/1.08    (~( ![A:$i,B:$i]:
% 0.87/1.08        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.87/1.08          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.87/1.08    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.87/1.08  thf('0', plain,
% 0.87/1.08      (((r2_hidden @ sk_B @ sk_A)
% 0.87/1.08        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.08  thf('1', plain,
% 0.87/1.08      (((r2_hidden @ sk_B @ sk_A)) | 
% 0.87/1.08       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.87/1.08      inference('split', [status(esa)], ['0'])).
% 0.87/1.08  thf('2', plain,
% 0.87/1.08      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.87/1.08      inference('split', [status(esa)], ['0'])).
% 0.87/1.08  thf(t69_enumset1, axiom,
% 0.87/1.08    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.87/1.08  thf('3', plain, (![X38 : $i]: ((k2_tarski @ X38 @ X38) = (k1_tarski @ X38))),
% 0.87/1.08      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.87/1.08  thf(t70_enumset1, axiom,
% 0.87/1.08    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.87/1.08  thf('4', plain,
% 0.87/1.08      (![X39 : $i, X40 : $i]:
% 0.87/1.08         ((k1_enumset1 @ X39 @ X39 @ X40) = (k2_tarski @ X39 @ X40))),
% 0.87/1.08      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.87/1.08  thf(d1_enumset1, axiom,
% 0.87/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.87/1.08     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.87/1.08       ( ![E:$i]:
% 0.87/1.08         ( ( r2_hidden @ E @ D ) <=>
% 0.87/1.08           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.87/1.08  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.87/1.08  thf(zf_stmt_2, axiom,
% 0.87/1.08    (![E:$i,C:$i,B:$i,A:$i]:
% 0.87/1.08     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.87/1.08       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.87/1.08  thf(zf_stmt_3, axiom,
% 0.87/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.87/1.08     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.87/1.08       ( ![E:$i]:
% 0.87/1.08         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.87/1.08  thf('5', plain,
% 0.87/1.08      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.87/1.08         ((zip_tseitin_0 @ X31 @ X32 @ X33 @ X34)
% 0.87/1.08          | (r2_hidden @ X31 @ X35)
% 0.87/1.08          | ((X35) != (k1_enumset1 @ X34 @ X33 @ X32)))),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.87/1.08  thf('6', plain,
% 0.87/1.08      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.87/1.08         ((r2_hidden @ X31 @ (k1_enumset1 @ X34 @ X33 @ X32))
% 0.87/1.08          | (zip_tseitin_0 @ X31 @ X32 @ X33 @ X34))),
% 0.87/1.08      inference('simplify', [status(thm)], ['5'])).
% 0.87/1.08  thf('7', plain,
% 0.87/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.08         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.87/1.08          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.87/1.08      inference('sup+', [status(thm)], ['4', '6'])).
% 0.87/1.08  thf('8', plain,
% 0.87/1.08      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.87/1.08         (((X27) != (X26)) | ~ (zip_tseitin_0 @ X27 @ X28 @ X29 @ X26))),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.87/1.08  thf('9', plain,
% 0.87/1.08      (![X26 : $i, X28 : $i, X29 : $i]:
% 0.87/1.08         ~ (zip_tseitin_0 @ X26 @ X28 @ X29 @ X26)),
% 0.87/1.08      inference('simplify', [status(thm)], ['8'])).
% 0.87/1.08  thf('10', plain,
% 0.87/1.08      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.87/1.08      inference('sup-', [status(thm)], ['7', '9'])).
% 0.87/1.08  thf('11', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.87/1.08      inference('sup+', [status(thm)], ['3', '10'])).
% 0.87/1.08  thf('12', plain,
% 0.87/1.08      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.87/1.08        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.08  thf('13', plain,
% 0.87/1.08      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.87/1.08         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.87/1.08      inference('split', [status(esa)], ['12'])).
% 0.87/1.08  thf(d5_xboole_0, axiom,
% 0.87/1.08    (![A:$i,B:$i,C:$i]:
% 0.87/1.08     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.87/1.08       ( ![D:$i]:
% 0.87/1.08         ( ( r2_hidden @ D @ C ) <=>
% 0.87/1.08           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.87/1.08  thf('14', plain,
% 0.87/1.08      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.87/1.08         (~ (r2_hidden @ X6 @ X5)
% 0.87/1.08          | ~ (r2_hidden @ X6 @ X4)
% 0.87/1.08          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.87/1.08      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.87/1.08  thf('15', plain,
% 0.87/1.08      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.87/1.08         (~ (r2_hidden @ X6 @ X4)
% 0.87/1.08          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.87/1.08      inference('simplify', [status(thm)], ['14'])).
% 0.87/1.08  thf('16', plain,
% 0.87/1.08      ((![X0 : $i]:
% 0.87/1.08          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 0.87/1.08         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.87/1.08      inference('sup-', [status(thm)], ['13', '15'])).
% 0.87/1.08  thf('17', plain,
% 0.87/1.08      ((~ (r2_hidden @ sk_B @ sk_A))
% 0.87/1.08         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.87/1.08      inference('sup-', [status(thm)], ['11', '16'])).
% 0.87/1.08  thf('18', plain,
% 0.87/1.08      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.87/1.08       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.87/1.08      inference('sup-', [status(thm)], ['2', '17'])).
% 0.87/1.08  thf('19', plain,
% 0.87/1.08      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.87/1.08       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.87/1.08      inference('split', [status(esa)], ['12'])).
% 0.87/1.08  thf(d10_xboole_0, axiom,
% 0.87/1.08    (![A:$i,B:$i]:
% 0.87/1.08     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.87/1.08  thf('20', plain,
% 0.87/1.08      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.87/1.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.87/1.08  thf('21', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.87/1.08      inference('simplify', [status(thm)], ['20'])).
% 0.87/1.08  thf(t12_xboole_1, axiom,
% 0.87/1.08    (![A:$i,B:$i]:
% 0.87/1.08     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.87/1.08  thf('22', plain,
% 0.87/1.08      (![X13 : $i, X14 : $i]:
% 0.87/1.08         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.87/1.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.87/1.08  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.87/1.08      inference('sup-', [status(thm)], ['21', '22'])).
% 0.87/1.08  thf(l27_zfmisc_1, axiom,
% 0.87/1.08    (![A:$i,B:$i]:
% 0.87/1.08     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.87/1.08  thf('24', plain,
% 0.87/1.08      (![X48 : $i, X49 : $i]:
% 0.87/1.08         ((r1_xboole_0 @ (k1_tarski @ X48) @ X49) | (r2_hidden @ X48 @ X49))),
% 0.87/1.08      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.87/1.08  thf(t87_xboole_1, axiom,
% 0.87/1.08    (![A:$i,B:$i,C:$i]:
% 0.87/1.08     ( ( r1_xboole_0 @ A @ B ) =>
% 0.87/1.08       ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 0.87/1.08         ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ))).
% 0.87/1.08  thf('25', plain,
% 0.87/1.08      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.87/1.08         (~ (r1_xboole_0 @ X23 @ X24)
% 0.87/1.08          | ((k2_xboole_0 @ (k4_xboole_0 @ X25 @ X23) @ X24)
% 0.87/1.08              = (k4_xboole_0 @ (k2_xboole_0 @ X25 @ X24) @ X23)))),
% 0.87/1.08      inference('cnf', [status(esa)], [t87_xboole_1])).
% 0.87/1.08  thf('26', plain,
% 0.87/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.08         ((r2_hidden @ X1 @ X0)
% 0.87/1.08          | ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k1_tarski @ X1)) @ X0)
% 0.87/1.08              = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ (k1_tarski @ X1))))),
% 0.87/1.08      inference('sup-', [status(thm)], ['24', '25'])).
% 0.87/1.08  thf('27', plain,
% 0.87/1.08      (![X0 : $i, X1 : $i]:
% 0.87/1.08         (((k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)
% 0.87/1.08            = (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.87/1.08          | (r2_hidden @ X1 @ X0))),
% 0.87/1.08      inference('sup+', [status(thm)], ['23', '26'])).
% 0.87/1.08  thf(commutativity_k2_xboole_0, axiom,
% 0.87/1.08    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.87/1.08  thf('28', plain,
% 0.87/1.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.87/1.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.87/1.08  thf(t36_xboole_1, axiom,
% 0.87/1.08    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.87/1.08  thf('29', plain,
% 0.87/1.08      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 0.87/1.08      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.87/1.08  thf('30', plain,
% 0.87/1.08      (![X13 : $i, X14 : $i]:
% 0.87/1.08         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.87/1.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.87/1.08  thf('31', plain,
% 0.87/1.08      (![X0 : $i, X1 : $i]:
% 0.87/1.08         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.87/1.08      inference('sup-', [status(thm)], ['29', '30'])).
% 0.87/1.08  thf('32', plain,
% 0.87/1.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.87/1.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.87/1.08  thf('33', plain,
% 0.87/1.08      (![X0 : $i, X1 : $i]:
% 0.87/1.08         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.87/1.08      inference('demod', [status(thm)], ['31', '32'])).
% 0.87/1.08  thf('34', plain,
% 0.87/1.08      (![X0 : $i, X1 : $i]:
% 0.87/1.08         (((X0) = (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.87/1.08          | (r2_hidden @ X1 @ X0))),
% 0.87/1.08      inference('demod', [status(thm)], ['27', '28', '33'])).
% 0.87/1.08  thf('35', plain,
% 0.87/1.08      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.87/1.08         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.87/1.08      inference('split', [status(esa)], ['0'])).
% 0.87/1.08  thf('36', plain,
% 0.87/1.08      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 0.87/1.08         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.87/1.08      inference('sup-', [status(thm)], ['34', '35'])).
% 0.87/1.08  thf('37', plain,
% 0.87/1.08      (((r2_hidden @ sk_B @ sk_A))
% 0.87/1.08         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.87/1.08      inference('simplify', [status(thm)], ['36'])).
% 0.87/1.08  thf('38', plain,
% 0.87/1.08      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.87/1.08      inference('split', [status(esa)], ['12'])).
% 0.87/1.08  thf('39', plain,
% 0.87/1.08      (((r2_hidden @ sk_B @ sk_A)) | 
% 0.87/1.08       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.87/1.08      inference('sup-', [status(thm)], ['37', '38'])).
% 0.87/1.08  thf('40', plain, ($false),
% 0.87/1.08      inference('sat_resolution*', [status(thm)], ['1', '18', '19', '39'])).
% 0.87/1.08  
% 0.87/1.08  % SZS output end Refutation
% 0.87/1.08  
% 0.87/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

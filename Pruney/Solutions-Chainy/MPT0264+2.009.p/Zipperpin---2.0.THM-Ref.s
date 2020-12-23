%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aZ1iUny4Z9

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:39 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   59 (  72 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :  374 ( 515 expanded)
%              Number of equality atoms :   40 (  57 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 )
      | ( X32 = X33 )
      | ( X32 = X34 )
      | ( X32 = X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k1_tarski @ A ) )
        & ( r2_hidden @ B @ C )
        & ( A != B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
            = ( k1_tarski @ A ) )
          & ( r2_hidden @ B @ C )
          & ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t59_zfmisc_1])).

thf('1',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('5',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X43: $i] :
      ( ( k2_tarski @ X43 @ X43 )
      = ( k1_tarski @ X43 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( r2_hidden @ X57 @ X58 )
      | ~ ( r1_tarski @ ( k2_tarski @ X57 @ X59 ) @ X58 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X57: $i,X59: $i,X60: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X57 @ X59 ) @ X60 )
      | ~ ( r2_hidden @ X59 @ X60 )
      | ~ ( r2_hidden @ X57 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('19',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( r2_hidden @ X59 @ X58 )
      | ~ ( r1_tarski @ ( k2_tarski @ X57 @ X59 ) @ X58 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('26',plain,(
    ! [X43: $i] :
      ( ( k2_tarski @ X43 @ X43 )
      = ( k1_tarski @ X43 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X41 @ X40 )
      | ~ ( zip_tseitin_0 @ X41 @ X37 @ X38 @ X39 )
      | ( X40
       != ( k1_enumset1 @ X39 @ X38 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,(
    ! [X37: $i,X38: $i,X39: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X37 @ X38 @ X39 )
      | ~ ( r2_hidden @ X41 @ ( k1_enumset1 @ X39 @ X38 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['0','31'])).

thf('33',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aZ1iUny4Z9
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.40/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.63  % Solved by: fo/fo7.sh
% 0.40/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.63  % done 418 iterations in 0.183s
% 0.40/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.63  % SZS output start Refutation
% 0.40/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.40/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.63  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.40/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.63  thf(d1_enumset1, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.63     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.40/0.63       ( ![E:$i]:
% 0.40/0.63         ( ( r2_hidden @ E @ D ) <=>
% 0.40/0.63           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.40/0.63  thf(zf_stmt_0, axiom,
% 0.40/0.63    (![E:$i,C:$i,B:$i,A:$i]:
% 0.40/0.63     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.40/0.63       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.40/0.63  thf('0', plain,
% 0.40/0.63      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.40/0.63         ((zip_tseitin_0 @ X32 @ X33 @ X34 @ X35)
% 0.40/0.63          | ((X32) = (X33))
% 0.40/0.63          | ((X32) = (X34))
% 0.40/0.63          | ((X32) = (X35)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(t59_zfmisc_1, conjecture,
% 0.40/0.63    (![A:$i,B:$i,C:$i]:
% 0.40/0.63     ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.40/0.63          ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ))).
% 0.40/0.63  thf(zf_stmt_1, negated_conjecture,
% 0.40/0.63    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.63        ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.40/0.63             ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ) )),
% 0.40/0.63    inference('cnf.neg', [status(esa)], [t59_zfmisc_1])).
% 0.40/0.63  thf('1', plain,
% 0.40/0.63      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.40/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.40/0.63  thf('2', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.63  thf('3', plain,
% 0.40/0.63      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_tarski @ sk_A))),
% 0.40/0.63      inference('demod', [status(thm)], ['1', '2'])).
% 0.40/0.63  thf(t17_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.40/0.63  thf('4', plain,
% 0.40/0.63      (![X18 : $i, X19 : $i]: (r1_tarski @ (k3_xboole_0 @ X18 @ X19) @ X18)),
% 0.40/0.63      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.40/0.63  thf('5', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_C)),
% 0.40/0.63      inference('sup+', [status(thm)], ['3', '4'])).
% 0.40/0.63  thf(t69_enumset1, axiom,
% 0.40/0.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.63  thf('6', plain, (![X43 : $i]: ((k2_tarski @ X43 @ X43) = (k1_tarski @ X43))),
% 0.40/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.63  thf(t38_zfmisc_1, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i]:
% 0.40/0.63     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.40/0.63       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.40/0.63  thf('7', plain,
% 0.40/0.63      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.40/0.63         ((r2_hidden @ X57 @ X58)
% 0.40/0.63          | ~ (r1_tarski @ (k2_tarski @ X57 @ X59) @ X58))),
% 0.40/0.63      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.40/0.63  thf('8', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.40/0.63      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.63  thf('9', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.40/0.63      inference('sup-', [status(thm)], ['5', '8'])).
% 0.40/0.63  thf('10', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.63  thf('11', plain,
% 0.40/0.63      (![X57 : $i, X59 : $i, X60 : $i]:
% 0.40/0.63         ((r1_tarski @ (k2_tarski @ X57 @ X59) @ X60)
% 0.40/0.63          | ~ (r2_hidden @ X59 @ X60)
% 0.40/0.63          | ~ (r2_hidden @ X57 @ X60))),
% 0.40/0.63      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.40/0.63  thf('12', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         (~ (r2_hidden @ X0 @ sk_C)
% 0.40/0.63          | (r1_tarski @ (k2_tarski @ X0 @ sk_B) @ sk_C))),
% 0.40/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.40/0.63  thf('13', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.40/0.63      inference('sup-', [status(thm)], ['9', '12'])).
% 0.40/0.63  thf(t28_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.63  thf('14', plain,
% 0.40/0.63      (![X22 : $i, X23 : $i]:
% 0.40/0.63         (((k3_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_tarski @ X22 @ X23))),
% 0.40/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.63  thf('15', plain,
% 0.40/0.63      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.40/0.63         = (k2_tarski @ sk_A @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.63  thf('16', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.63  thf('17', plain,
% 0.40/0.63      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.40/0.63         = (k2_tarski @ sk_A @ sk_B))),
% 0.40/0.63      inference('demod', [status(thm)], ['15', '16'])).
% 0.40/0.63  thf('18', plain,
% 0.40/0.63      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_tarski @ sk_A))),
% 0.40/0.63      inference('demod', [status(thm)], ['1', '2'])).
% 0.40/0.63  thf('19', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_A))),
% 0.40/0.63      inference('sup+', [status(thm)], ['17', '18'])).
% 0.40/0.63  thf(d10_xboole_0, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.63  thf('20', plain,
% 0.40/0.63      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.63  thf('21', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.40/0.63      inference('simplify', [status(thm)], ['20'])).
% 0.40/0.63  thf('22', plain,
% 0.40/0.63      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.40/0.63         ((r2_hidden @ X59 @ X58)
% 0.40/0.63          | ~ (r1_tarski @ (k2_tarski @ X57 @ X59) @ X58))),
% 0.40/0.63      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.40/0.63  thf('23', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.63  thf('24', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.40/0.63      inference('sup+', [status(thm)], ['19', '23'])).
% 0.40/0.63  thf(t70_enumset1, axiom,
% 0.40/0.63    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.40/0.63  thf('25', plain,
% 0.40/0.63      (![X44 : $i, X45 : $i]:
% 0.40/0.63         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 0.40/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.63  thf('26', plain,
% 0.40/0.63      (![X43 : $i]: ((k2_tarski @ X43 @ X43) = (k1_tarski @ X43))),
% 0.40/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.63  thf('27', plain,
% 0.40/0.63      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['25', '26'])).
% 0.40/0.63  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.40/0.63  thf(zf_stmt_3, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.63     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.40/0.63       ( ![E:$i]:
% 0.40/0.63         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.40/0.63  thf('28', plain,
% 0.40/0.63      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.40/0.63         (~ (r2_hidden @ X41 @ X40)
% 0.40/0.63          | ~ (zip_tseitin_0 @ X41 @ X37 @ X38 @ X39)
% 0.40/0.63          | ((X40) != (k1_enumset1 @ X39 @ X38 @ X37)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.63  thf('29', plain,
% 0.40/0.63      (![X37 : $i, X38 : $i, X39 : $i, X41 : $i]:
% 0.40/0.63         (~ (zip_tseitin_0 @ X41 @ X37 @ X38 @ X39)
% 0.40/0.63          | ~ (r2_hidden @ X41 @ (k1_enumset1 @ X39 @ X38 @ X37)))),
% 0.40/0.63      inference('simplify', [status(thm)], ['28'])).
% 0.40/0.63  thf('30', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.40/0.63          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['27', '29'])).
% 0.40/0.63  thf('31', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A)),
% 0.40/0.63      inference('sup-', [status(thm)], ['24', '30'])).
% 0.40/0.63  thf('32', plain,
% 0.40/0.63      ((((sk_B) = (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['0', '31'])).
% 0.40/0.63  thf('33', plain, (((sk_B) = (sk_A))),
% 0.40/0.63      inference('simplify', [status(thm)], ['32'])).
% 0.40/0.63  thf('34', plain, (((sk_A) != (sk_B))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.63  thf('35', plain, ($false),
% 0.40/0.63      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.40/0.63  
% 0.40/0.63  % SZS output end Refutation
% 0.40/0.63  
% 0.49/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

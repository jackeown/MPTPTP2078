%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8YjQveOhwd

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  73 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :  307 ( 701 expanded)
%              Number of equality atoms :   35 (  71 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
       => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
          & ( ( ( k2_mcart_1 @ A )
              = C )
            | ( ( k2_mcart_1 @ A )
              = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_mcart_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X14 ) @ X16 )
      | ~ ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('3',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X12 @ X12 @ X13 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
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

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ~ ( zip_tseitin_0 @ ( k2_mcart_1 @ sk_A ) @ sk_D @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('10',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_D )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_C ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X14 ) @ X15 )
      | ~ ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('15',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('17',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('19',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['17','18'])).

thf('20',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['12','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('22',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('24',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference('sat_resolution*',[status(thm)],['17','23'])).

thf('25',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference(simpl_trail,[status(thm)],['22','24'])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','20','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8YjQveOhwd
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 21 iterations in 0.009s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.45  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.45  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.45  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.45  thf(d1_enumset1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.45     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.45       ( ![E:$i]:
% 0.20/0.45         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.45           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, axiom,
% 0.20/0.45    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.45     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.45       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.45         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.20/0.45          | ((X1) = (X2))
% 0.20/0.45          | ((X1) = (X3))
% 0.20/0.45          | ((X1) = (X4)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t16_mcart_1, conjecture,
% 0.20/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.45     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.20/0.45       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.45         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_1, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.45        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.20/0.45          ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.45            ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t16_mcart_1])).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k2_tarski @ sk_C @ sk_D)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.45  thf(t10_mcart_1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.45       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.45         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.45         ((r2_hidden @ (k2_mcart_1 @ X14) @ X16)
% 0.20/0.45          | ~ (r2_hidden @ X14 @ (k2_zfmisc_1 @ X15 @ X16)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k2_tarski @ sk_C @ sk_D))),
% 0.20/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.45  thf(t70_enumset1, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X12 : $i, X13 : $i]:
% 0.20/0.45         ((k1_enumset1 @ X12 @ X12 @ X13) = (k2_tarski @ X12 @ X13))),
% 0.20/0.45      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.45  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.45  thf(zf_stmt_3, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.45     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.45       ( ![E:$i]:
% 0.20/0.45         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.45         (~ (r2_hidden @ X10 @ X9)
% 0.20/0.45          | ~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.20/0.45          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.20/0.45         (~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.20/0.45          | ~ (r2_hidden @ X10 @ (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.20/0.45      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.45         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.45          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.45      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      (~ (zip_tseitin_0 @ (k2_mcart_1 @ sk_A) @ sk_D @ sk_C @ sk_C)),
% 0.20/0.45      inference('sup-', [status(thm)], ['3', '7'])).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      ((((k2_mcart_1 @ sk_A) = (sk_C))
% 0.20/0.45        | ((k2_mcart_1 @ sk_A) = (sk_C))
% 0.20/0.45        | ((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '8'])).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      ((((k2_mcart_1 @ sk_A) = (sk_D)) | ((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.20/0.45      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.20/0.45        | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.45  thf('12', plain,
% 0.20/0.45      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.20/0.45         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.20/0.45      inference('split', [status(esa)], ['11'])).
% 0.20/0.45  thf('13', plain,
% 0.20/0.45      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k2_tarski @ sk_C @ sk_D)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.45  thf('14', plain,
% 0.20/0.45      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.45         ((r2_hidden @ (k1_mcart_1 @ X14) @ X15)
% 0.20/0.45          | ~ (r2_hidden @ X14 @ (k2_zfmisc_1 @ X15 @ X16)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.45  thf('15', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.20/0.45      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.45  thf('16', plain,
% 0.20/0.45      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))
% 0.20/0.45         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)))),
% 0.20/0.45      inference('split', [status(esa)], ['11'])).
% 0.20/0.45  thf('17', plain, (((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.45  thf('18', plain,
% 0.20/0.45      (~ (((k2_mcart_1 @ sk_A) = (sk_C))) | 
% 0.20/0.45       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.20/0.45      inference('split', [status(esa)], ['11'])).
% 0.20/0.45  thf('19', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.20/0.45      inference('sat_resolution*', [status(thm)], ['17', '18'])).
% 0.20/0.45  thf('20', plain, (((k2_mcart_1 @ sk_A) != (sk_C))),
% 0.20/0.45      inference('simpl_trail', [status(thm)], ['12', '19'])).
% 0.20/0.45  thf('21', plain,
% 0.20/0.45      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.20/0.45        | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.45  thf('22', plain,
% 0.20/0.45      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.20/0.45         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.20/0.45      inference('split', [status(esa)], ['21'])).
% 0.20/0.45  thf('23', plain,
% 0.20/0.45      (~ (((k2_mcart_1 @ sk_A) = (sk_D))) | 
% 0.20/0.45       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.20/0.45      inference('split', [status(esa)], ['21'])).
% 0.20/0.45  thf('24', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.20/0.45      inference('sat_resolution*', [status(thm)], ['17', '23'])).
% 0.20/0.45  thf('25', plain, (((k2_mcart_1 @ sk_A) != (sk_D))),
% 0.20/0.45      inference('simpl_trail', [status(thm)], ['22', '24'])).
% 0.20/0.45  thf('26', plain, ($false),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['10', '20', '25'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

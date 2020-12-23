%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J9XfCT8od5

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  77 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  363 ( 757 expanded)
%              Number of equality atoms :   41 (  77 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 @ X23 )
      | ( X19 = X20 )
      | ( X19 = X21 )
      | ( X19 = X22 )
      | ( X19 = X23 ) ) ),
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
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k2_tarski @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X32 ) @ X34 )
      | ~ ( r2_hidden @ X32 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('3',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ~ ( zip_tseitin_0 @ X30 @ X25 @ X26 @ X27 @ X28 )
      | ( X29
       != ( k2_enumset1 @ X28 @ X27 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X25 @ X26 @ X27 @ X28 )
      | ~ ( r2_hidden @ X30 @ ( k2_enumset1 @ X28 @ X27 @ X26 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ~ ( zip_tseitin_0 @ ( k2_mcart_1 @ sk_A ) @ sk_D @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C_1 )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_C_1 )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_C_1 )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_D )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_C_1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k2_tarski @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X32 ) @ X33 )
      | ~ ( r2_hidden @ X32 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('17',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('19',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('21',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['19','20'])).

thf('22',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C_1 ),
    inference(simpl_trail,[status(thm)],['14','21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('24',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['23'])).

thf('26',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference('sat_resolution*',[status(thm)],['19','25'])).

thf('27',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference(simpl_trail,[status(thm)],['24','26'])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','22','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J9XfCT8od5
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:00:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 133 iterations in 0.063s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.51  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(d2_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.51     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.20/0.51       ( ![F:$i]:
% 0.20/0.51         ( ( r2_hidden @ F @ E ) <=>
% 0.20/0.51           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.20/0.51                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, axiom,
% 0.20/0.51    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.51     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.20/0.51       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.20/0.51         ( ( F ) != ( D ) ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.51         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.20/0.51          | ((X19) = (X20))
% 0.20/0.51          | ((X19) = (X21))
% 0.20/0.51          | ((X19) = (X22))
% 0.20/0.51          | ((X19) = (X23)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t16_mcart_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.20/0.51       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.51         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_1, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.20/0.51          ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.51            ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t16_mcart_1])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k2_tarski @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.51  thf(t10_mcart_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.51       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.51         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.51         ((r2_hidden @ (k2_mcart_1 @ X32) @ X34)
% 0.20/0.51          | ~ (r2_hidden @ X32 @ (k2_zfmisc_1 @ X33 @ X34)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf(t70_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]:
% 0.20/0.51         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.51  thf(t71_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.51         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.51  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.20/0.51  thf(zf_stmt_3, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.51     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.20/0.51       ( ![F:$i]:
% 0.20/0.51         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X30 @ X29)
% 0.20/0.51          | ~ (zip_tseitin_0 @ X30 @ X25 @ X26 @ X27 @ X28)
% 0.20/0.51          | ((X29) != (k2_enumset1 @ X28 @ X27 @ X26 @ X25)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X30 : $i]:
% 0.20/0.51         (~ (zip_tseitin_0 @ X30 @ X25 @ X26 @ X27 @ X28)
% 0.20/0.51          | ~ (r2_hidden @ X30 @ (k2_enumset1 @ X28 @ X27 @ X26 @ X25)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.20/0.51          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.51          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (~ (zip_tseitin_0 @ (k2_mcart_1 @ sk_A) @ sk_D @ sk_C_1 @ sk_C_1 @ sk_C_1)),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      ((((k2_mcart_1 @ sk_A) = (sk_C_1))
% 0.20/0.51        | ((k2_mcart_1 @ sk_A) = (sk_C_1))
% 0.20/0.51        | ((k2_mcart_1 @ sk_A) = (sk_C_1))
% 0.20/0.51        | ((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      ((((k2_mcart_1 @ sk_A) = (sk_D)) | ((k2_mcart_1 @ sk_A) = (sk_C_1)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.20/0.51        | ((k2_mcart_1 @ sk_A) != (sk_C_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      ((((k2_mcart_1 @ sk_A) != (sk_C_1)))
% 0.20/0.51         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k2_tarski @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.51         ((r2_hidden @ (k1_mcart_1 @ X32) @ X33)
% 0.20/0.51          | ~ (r2_hidden @ X32 @ (k2_zfmisc_1 @ X33 @ X34)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.51  thf('17', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))
% 0.20/0.51         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['13'])).
% 0.20/0.51  thf('19', plain, (((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (~ (((k2_mcart_1 @ sk_A) = (sk_C_1))) | 
% 0.20/0.51       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.20/0.51      inference('split', [status(esa)], ['13'])).
% 0.20/0.51  thf('21', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C_1)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('22', plain, (((k2_mcart_1 @ sk_A) != (sk_C_1))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['14', '21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.20/0.51        | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.20/0.51         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.20/0.51      inference('split', [status(esa)], ['23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (~ (((k2_mcart_1 @ sk_A) = (sk_D))) | 
% 0.20/0.51       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.20/0.51      inference('split', [status(esa)], ['23'])).
% 0.20/0.51  thf('26', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['19', '25'])).
% 0.20/0.51  thf('27', plain, (((k2_mcart_1 @ sk_A) != (sk_D))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['24', '26'])).
% 0.20/0.51  thf('28', plain, ($false),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['12', '22', '27'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

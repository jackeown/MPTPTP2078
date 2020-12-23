%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HxAkSe3r1C

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:42 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   52 (  63 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  400 ( 541 expanded)
%              Number of equality atoms :   40 (  50 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(d3_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( ( G != E )
              & ( G != D )
              & ( G != C )
              & ( G != B )
              & ( G != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [G: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A )
    <=> ( ( G != A )
        & ( G != B )
        & ( G != C )
        & ( G != D )
        & ( G != E ) ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 )
      | ( X20 = X21 )
      | ( X20 = X22 )
      | ( X20 = X23 )
      | ( X20 = X24 )
      | ( X20 = X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_mcart_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X45 ) @ X46 )
      | ~ ( r2_hidden @ X45 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('3',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X8 @ X8 @ X9 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X10 @ X10 @ X11 @ X12 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X32 )
      | ~ ( zip_tseitin_0 @ X33 @ X27 @ X28 @ X29 @ X30 @ X31 )
      | ( X32
       != ( k3_enumset1 @ X31 @ X30 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X27 @ X28 @ X29 @ X30 @ X31 )
      | ~ ( r2_hidden @ X33 @ ( k3_enumset1 @ X31 @ X30 @ X29 @ X28 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,(
    ~ ( zip_tseitin_0 @ ( k1_mcart_1 @ sk_A ) @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('16',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('20',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X45 ) @ X47 )
      | ~ ( r2_hidden @ X45 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('21',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('23',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('25',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['23','24'])).

thf('26',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['18','25'])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['16','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HxAkSe3r1C
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:21:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.57  % Solved by: fo/fo7.sh
% 0.36/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.57  % done 229 iterations in 0.111s
% 0.36/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.57  % SZS output start Refutation
% 0.36/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.57  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.36/0.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.36/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.57  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.36/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 0.36/0.57  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.36/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.36/0.57  thf(d3_enumset1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.57     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.36/0.57       ( ![G:$i]:
% 0.36/0.57         ( ( r2_hidden @ G @ F ) <=>
% 0.36/0.57           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 0.36/0.57                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 0.36/0.57  thf(zf_stmt_0, axiom,
% 0.36/0.57    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.36/0.57     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 0.36/0.57       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 0.36/0.57         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 0.36/0.57  thf('0', plain,
% 0.36/0.57      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.57         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25)
% 0.36/0.57          | ((X20) = (X21))
% 0.36/0.57          | ((X20) = (X22))
% 0.36/0.57          | ((X20) = (X23))
% 0.36/0.57          | ((X20) = (X24))
% 0.36/0.57          | ((X20) = (X25)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t12_mcart_1, conjecture,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.36/0.57       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.36/0.57         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.36/0.57  thf(zf_stmt_1, negated_conjecture,
% 0.36/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.57        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.36/0.57          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.36/0.57            ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )),
% 0.36/0.57    inference('cnf.neg', [status(esa)], [t12_mcart_1])).
% 0.36/0.57  thf('1', plain,
% 0.36/0.57      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C_1))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.57  thf(t10_mcart_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.36/0.57       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.36/0.57         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.36/0.57  thf('2', plain,
% 0.36/0.57      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.36/0.57         ((r2_hidden @ (k1_mcart_1 @ X45) @ X46)
% 0.36/0.57          | ~ (r2_hidden @ X45 @ (k2_zfmisc_1 @ X46 @ X47)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.36/0.57  thf('3', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.36/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.57  thf(t69_enumset1, axiom,
% 0.36/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.57  thf('4', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.36/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.57  thf(t70_enumset1, axiom,
% 0.36/0.57    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.36/0.57  thf('5', plain,
% 0.36/0.57      (![X8 : $i, X9 : $i]:
% 0.36/0.57         ((k1_enumset1 @ X8 @ X8 @ X9) = (k2_tarski @ X8 @ X9))),
% 0.36/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.57  thf(t71_enumset1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.36/0.57  thf('6', plain,
% 0.36/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.57         ((k2_enumset1 @ X10 @ X10 @ X11 @ X12)
% 0.36/0.57           = (k1_enumset1 @ X10 @ X11 @ X12))),
% 0.36/0.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.36/0.57  thf(t72_enumset1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.57     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.36/0.57  thf('7', plain,
% 0.36/0.57      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.57         ((k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16)
% 0.36/0.57           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 0.36/0.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.36/0.57  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 0.36/0.57  thf(zf_stmt_3, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.57     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.36/0.57       ( ![G:$i]:
% 0.36/0.57         ( ( r2_hidden @ G @ F ) <=>
% 0.36/0.57           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.36/0.57  thf('8', plain,
% 0.36/0.57      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.36/0.57         (~ (r2_hidden @ X33 @ X32)
% 0.36/0.57          | ~ (zip_tseitin_0 @ X33 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.36/0.57          | ((X32) != (k3_enumset1 @ X31 @ X30 @ X29 @ X28 @ X27)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.36/0.57  thf('9', plain,
% 0.36/0.57      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X33 : $i]:
% 0.36/0.57         (~ (zip_tseitin_0 @ X33 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.36/0.57          | ~ (r2_hidden @ X33 @ (k3_enumset1 @ X31 @ X30 @ X29 @ X28 @ X27)))),
% 0.36/0.57      inference('simplify', [status(thm)], ['8'])).
% 0.36/0.57  thf('10', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.57         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.36/0.57          | ~ (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 0.36/0.57      inference('sup-', [status(thm)], ['7', '9'])).
% 0.36/0.57  thf('11', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.57         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.36/0.57          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2))),
% 0.36/0.57      inference('sup-', [status(thm)], ['6', '10'])).
% 0.36/0.57  thf('12', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.57         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.36/0.57          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1))),
% 0.36/0.57      inference('sup-', [status(thm)], ['5', '11'])).
% 0.36/0.57  thf('13', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.36/0.57          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['4', '12'])).
% 0.36/0.57  thf('14', plain,
% 0.36/0.57      (~ (zip_tseitin_0 @ (k1_mcart_1 @ sk_A) @ sk_B @ sk_B @ sk_B @ sk_B @ 
% 0.36/0.57          sk_B)),
% 0.36/0.57      inference('sup-', [status(thm)], ['3', '13'])).
% 0.36/0.57  thf('15', plain,
% 0.36/0.57      ((((k1_mcart_1 @ sk_A) = (sk_B))
% 0.36/0.57        | ((k1_mcart_1 @ sk_A) = (sk_B))
% 0.36/0.57        | ((k1_mcart_1 @ sk_A) = (sk_B))
% 0.36/0.57        | ((k1_mcart_1 @ sk_A) = (sk_B))
% 0.36/0.57        | ((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['0', '14'])).
% 0.36/0.57  thf('16', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.36/0.57      inference('simplify', [status(thm)], ['15'])).
% 0.36/0.57  thf('17', plain,
% 0.36/0.57      ((((k1_mcart_1 @ sk_A) != (sk_B))
% 0.36/0.57        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.57  thf('18', plain,
% 0.36/0.57      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.36/0.57         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.36/0.57      inference('split', [status(esa)], ['17'])).
% 0.36/0.57  thf('19', plain,
% 0.36/0.57      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C_1))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.57  thf('20', plain,
% 0.36/0.57      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.36/0.57         ((r2_hidden @ (k2_mcart_1 @ X45) @ X47)
% 0.36/0.57          | ~ (r2_hidden @ X45 @ (k2_zfmisc_1 @ X46 @ X47)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.36/0.57  thf('21', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1)),
% 0.36/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.57  thf('22', plain,
% 0.36/0.57      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))
% 0.36/0.57         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1)))),
% 0.36/0.57      inference('split', [status(esa)], ['17'])).
% 0.36/0.57  thf('23', plain, (((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))),
% 0.36/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.57  thf('24', plain,
% 0.36/0.57      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.36/0.57       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))),
% 0.36/0.57      inference('split', [status(esa)], ['17'])).
% 0.36/0.57  thf('25', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.36/0.57      inference('sat_resolution*', [status(thm)], ['23', '24'])).
% 0.36/0.57  thf('26', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.36/0.57      inference('simpl_trail', [status(thm)], ['18', '25'])).
% 0.36/0.57  thf('27', plain, ($false),
% 0.36/0.57      inference('simplify_reflect-', [status(thm)], ['16', '26'])).
% 0.36/0.57  
% 0.36/0.57  % SZS output end Refutation
% 0.36/0.57  
% 0.36/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

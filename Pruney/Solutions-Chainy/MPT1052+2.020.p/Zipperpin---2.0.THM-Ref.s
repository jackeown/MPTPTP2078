%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kZzSwuScUD

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  73 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  242 ( 693 expanded)
%              Number of equality atoms :   20 (  48 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t169_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
       => ( ( ( k1_relat_1 @ C )
            = A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
         => ( ( ( k1_relat_1 @ C )
              = A )
            & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t169_funct_2])).

thf('0',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( ( v1_relat_1 @ E )
              & ( v1_funct_1 @ E )
              & ( D = E )
              & ( ( k1_relat_1 @ E )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( ( k1_relat_1 @ E )
          = A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X10 @ X7 @ X8 ) @ X10 @ X7 @ X8 )
      | ( X9
       != ( k1_funct_2 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X10 @ X7 @ X8 ) @ X10 @ X7 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_funct_2 @ X8 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2 = X0 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( sk_C
    = ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    zip_tseitin_0 @ sk_C @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = X3 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_C )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ( sk_A != sk_A )
   <= ( ( k1_relat_1 @ sk_C )
     != sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf('18',plain,(
    zip_tseitin_0 @ sk_C @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['17','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kZzSwuScUD
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 38 iterations in 0.027s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(t169_funct_2, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.48       ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.21/0.48         ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.21/0.48           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.48        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.48          ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.21/0.48            ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.21/0.48              ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t169_funct_2])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((((k1_relat_1 @ sk_C) != (sk_A))
% 0.21/0.48        | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))
% 0.21/0.48         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('2', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d2_funct_2, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.21/0.48       ( ![D:$i]:
% 0.21/0.48         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.48           ( ?[E:$i]:
% 0.21/0.48             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.21/0.48               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.21/0.48               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.48  thf(zf_stmt_2, axiom,
% 0.21/0.48    (![E:$i,D:$i,B:$i,A:$i]:
% 0.21/0.48     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.21/0.48       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.21/0.48         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.21/0.48         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.21/0.48  thf(zf_stmt_3, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.21/0.48       ( ![D:$i]:
% 0.21/0.48         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.48           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X10 @ X9)
% 0.21/0.48          | (zip_tseitin_0 @ (sk_E_1 @ X10 @ X7 @ X8) @ X10 @ X7 @ X8)
% 0.21/0.48          | ((X9) != (k1_funct_2 @ X8 @ X7)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.48         ((zip_tseitin_0 @ (sk_E_1 @ X10 @ X7 @ X8) @ X10 @ X7 @ X8)
% 0.21/0.48          | ~ (r2_hidden @ X10 @ (k1_funct_2 @ X8 @ X7)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      ((zip_tseitin_0 @ (sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C @ sk_B @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      ((zip_tseitin_0 @ (sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C @ sk_B @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (((X2) = (X0)) | ~ (zip_tseitin_0 @ X0 @ X2 @ X1 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.48  thf('8', plain, (((sk_C) = (sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain, ((zip_tseitin_0 @ sk_C @ sk_C @ sk_B @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['5', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (((k1_relat_1 @ X0) = (X3)) | ~ (zip_tseitin_0 @ X0 @ X2 @ X1 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.48  thf('11', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      ((((k1_relat_1 @ sk_C) != (sk_A)))
% 0.21/0.48         <= (~ (((k1_relat_1 @ sk_C) = (sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      ((((sk_A) != (sk_A))) <= (~ (((k1_relat_1 @ sk_C) = (sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('14', plain, ((((k1_relat_1 @ sk_C) = (sk_A)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)) | 
% 0.21/0.48       ~ (((k1_relat_1 @ sk_C) = (sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('16', plain, (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.21/0.48  thf('18', plain, ((zip_tseitin_0 @ sk_C @ sk_C @ sk_B @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['5', '8'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.21/0.48          | ~ (zip_tseitin_0 @ X0 @ X2 @ X1 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.48  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain, ($false), inference('demod', [status(thm)], ['17', '20'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

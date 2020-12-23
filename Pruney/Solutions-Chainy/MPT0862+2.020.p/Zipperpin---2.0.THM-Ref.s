%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HDgCp514aH

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  61 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  210 ( 617 expanded)
%              Number of equality atoms :   36 ( 100 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t18_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( ( ( k2_mcart_1 @ A )
              = C )
            | ( ( k2_mcart_1 @ A )
              = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k2_mcart_1 @ X3 )
        = X6 )
      | ( ( k2_mcart_1 @ X3 )
        = X5 )
      | ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X4 @ ( k2_tarski @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_mcart_1])).

thf('2',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_mcart_1 @ X1 )
        = X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('7',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( sk_B != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('13',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference('sat_resolution*',[status(thm)],['11','12'])).

thf('14',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference(simpl_trail,[status(thm)],['4','13'])).

thf('15',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('16',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('17',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['11','16'])).

thf('18',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['15','17'])).

thf('19',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['2','14','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HDgCp514aH
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:52:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 16 iterations in 0.012s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.46  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(t18_mcart_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( r2_hidden @
% 0.20/0.46         A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.20/0.46       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.20/0.46         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46        ( ( r2_hidden @
% 0.20/0.46            A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.20/0.46          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.20/0.46            ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t18_mcart_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      ((r2_hidden @ sk_A @ 
% 0.20/0.46        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t16_mcart_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.20/0.46       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.46         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.46         (((k2_mcart_1 @ X3) = (X6))
% 0.20/0.46          | ((k2_mcart_1 @ X3) = (X5))
% 0.20/0.46          | ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X4 @ (k2_tarski @ X5 @ X6))))),
% 0.20/0.46      inference('cnf', [status(esa)], [t16_mcart_1])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      ((((k2_mcart_1 @ sk_A) = (sk_C)) | ((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.20/0.46         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.20/0.46      inference('split', [status(esa)], ['3'])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      ((r2_hidden @ sk_A @ 
% 0.20/0.46        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t12_mcart_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.20/0.46       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.20/0.46         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (((k1_mcart_1 @ X1) = (X0))
% 0.20/0.46          | ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ (k1_tarski @ X0) @ X2)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.20/0.46  thf('7', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.20/0.46         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.20/0.46      inference('split', [status(esa)], ['8'])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      ((((sk_B) != (sk_B))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.46  thf('11', plain, ((((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (~ (((k2_mcart_1 @ sk_A) = (sk_D))) | ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.20/0.46      inference('split', [status(esa)], ['3'])).
% 0.20/0.46  thf('13', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf('14', plain, (((k2_mcart_1 @ sk_A) != (sk_D))),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['4', '13'])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.20/0.46         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.20/0.46      inference('split', [status(esa)], ['8'])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (~ (((k2_mcart_1 @ sk_A) = (sk_C))) | ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.20/0.46      inference('split', [status(esa)], ['8'])).
% 0.20/0.46  thf('17', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['11', '16'])).
% 0.20/0.46  thf('18', plain, (((k2_mcart_1 @ sk_A) != (sk_C))),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['15', '17'])).
% 0.20/0.46  thf('19', plain, ($false),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['2', '14', '18'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

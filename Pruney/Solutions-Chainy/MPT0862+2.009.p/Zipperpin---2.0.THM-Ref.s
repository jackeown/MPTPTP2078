%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qs0csZgqWf

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  65 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  231 ( 652 expanded)
%              Number of equality atoms :   40 ( 105 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X22 ) @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ ( k1_tarski @ X21 ) @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('4',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D_1 ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_mcart_1 @ X22 )
        = X21 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ ( k1_tarski @ X21 ) @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('10',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( sk_B != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('16',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['14','15'])).

thf('17',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D_1 ),
    inference(simpl_trail,[status(thm)],['7','16'])).

thf('18',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('19',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('20',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['14','19'])).

thf('21',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['18','20'])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['5','17','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qs0csZgqWf
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 38 iterations in 0.019s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.47  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.47  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.47  thf(t18_mcart_1, conjecture,
% 0.22/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.47     ( ( r2_hidden @
% 0.22/0.47         A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.22/0.47       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.22/0.47         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.47        ( ( r2_hidden @
% 0.22/0.47            A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.22/0.47          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.22/0.47            ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t18_mcart_1])).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      ((r2_hidden @ sk_A @ 
% 0.22/0.47        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t12_mcart_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.22/0.47       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.22/0.47         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.47         ((r2_hidden @ (k2_mcart_1 @ X22) @ X23)
% 0.22/0.47          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ (k1_tarski @ X21) @ X23)))),
% 0.22/0.47      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.22/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.47  thf(d2_tarski, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.22/0.47       ( ![D:$i]:
% 0.22/0.47         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X4 @ X2)
% 0.22/0.47          | ((X4) = (X3))
% 0.22/0.47          | ((X4) = (X0))
% 0.22/0.47          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.22/0.47      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.22/0.47         (((X4) = (X0))
% 0.22/0.47          | ((X4) = (X3))
% 0.22/0.47          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.22/0.47      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      ((((k2_mcart_1 @ sk_A) = (sk_C)) | ((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['2', '4'])).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      ((((k2_mcart_1 @ sk_A) != (sk_D_1)))
% 0.22/0.47         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.22/0.47      inference('split', [status(esa)], ['6'])).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      ((r2_hidden @ sk_A @ 
% 0.22/0.47        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.47         (((k1_mcart_1 @ X22) = (X21))
% 0.22/0.47          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ (k1_tarski @ X21) @ X23)))),
% 0.22/0.47      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.22/0.47  thf('10', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.22/0.47         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.22/0.47      inference('split', [status(esa)], ['11'])).
% 0.22/0.47  thf('13', plain,
% 0.22/0.47      ((((sk_B) != (sk_B))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.22/0.47      inference('sup-', [status(thm)], ['10', '12'])).
% 0.22/0.47  thf('14', plain, ((((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.22/0.47      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.47  thf('15', plain,
% 0.22/0.47      (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))) | 
% 0.22/0.47       ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.22/0.47      inference('split', [status(esa)], ['6'])).
% 0.22/0.47  thf('16', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.22/0.47      inference('sat_resolution*', [status(thm)], ['14', '15'])).
% 0.22/0.47  thf('17', plain, (((k2_mcart_1 @ sk_A) != (sk_D_1))),
% 0.22/0.47      inference('simpl_trail', [status(thm)], ['7', '16'])).
% 0.22/0.47  thf('18', plain,
% 0.22/0.47      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.22/0.47         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.22/0.47      inference('split', [status(esa)], ['11'])).
% 0.22/0.47  thf('19', plain,
% 0.22/0.47      (~ (((k2_mcart_1 @ sk_A) = (sk_C))) | ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.22/0.47      inference('split', [status(esa)], ['11'])).
% 0.22/0.47  thf('20', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.22/0.47      inference('sat_resolution*', [status(thm)], ['14', '19'])).
% 0.22/0.47  thf('21', plain, (((k2_mcart_1 @ sk_A) != (sk_C))),
% 0.22/0.47      inference('simpl_trail', [status(thm)], ['18', '20'])).
% 0.22/0.47  thf('22', plain, ($false),
% 0.22/0.47      inference('simplify_reflect-', [status(thm)], ['5', '17', '21'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

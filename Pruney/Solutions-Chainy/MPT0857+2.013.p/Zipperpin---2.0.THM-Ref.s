%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fbCESzpNFl

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  44 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  185 ( 326 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t13_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( k2_mcart_1 @ A )
          = C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
       => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
          & ( ( k2_mcart_1 @ A )
            = C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k1_tarski @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X10 ) @ X12 )
      | ~ ( r2_hidden @ X10 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X4 ) @ ( k1_tarski @ X5 ) )
        = ( k1_tarski @ X4 ) )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X8 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X7 @ ( k1_tarski @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X7 @ ( k1_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( sk_C
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k1_tarski @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X10 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('12',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('14',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('16',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['14','15'])).

thf('17',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['9','16'])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['7','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fbCESzpNFl
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:03:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 24 iterations in 0.015s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.45  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.45  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.45  thf(t13_mcart_1, conjecture,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.21/0.45       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.45         ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.45        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.21/0.45          ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.45            ( ( k2_mcart_1 @ A ) = ( C ) ) ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t13_mcart_1])).
% 0.21/0.45  thf('0', plain,
% 0.21/0.45      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k1_tarski @ sk_C)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(t10_mcart_1, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.45       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.45         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.45  thf('1', plain,
% 0.21/0.45      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.45         ((r2_hidden @ (k2_mcart_1 @ X10) @ X12)
% 0.21/0.45          | ~ (r2_hidden @ X10 @ (k2_zfmisc_1 @ X11 @ X12)))),
% 0.21/0.45      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.45  thf('2', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))),
% 0.21/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.45  thf(t20_zfmisc_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.45         ( k1_tarski @ A ) ) <=>
% 0.21/0.45       ( ( A ) != ( B ) ) ))).
% 0.21/0.45  thf('3', plain,
% 0.21/0.45      (![X4 : $i, X5 : $i]:
% 0.21/0.45         (((k4_xboole_0 @ (k1_tarski @ X4) @ (k1_tarski @ X5))
% 0.21/0.45            = (k1_tarski @ X4))
% 0.21/0.45          | ((X4) = (X5)))),
% 0.21/0.45      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.45  thf(t64_zfmisc_1, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.21/0.45       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.45  thf('4', plain,
% 0.21/0.45      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.45         (((X6) != (X8))
% 0.21/0.45          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X7 @ (k1_tarski @ X8))))),
% 0.21/0.45      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.21/0.45  thf('5', plain,
% 0.21/0.45      (![X7 : $i, X8 : $i]:
% 0.21/0.45         ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X7 @ (k1_tarski @ X8)))),
% 0.21/0.45      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.45  thf('6', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.45  thf('7', plain, (((sk_C) = (k2_mcart_1 @ sk_A))),
% 0.21/0.45      inference('sup-', [status(thm)], ['2', '6'])).
% 0.21/0.45  thf('8', plain,
% 0.21/0.45      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.21/0.45        | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('9', plain,
% 0.21/0.45      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.21/0.45         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.45      inference('split', [status(esa)], ['8'])).
% 0.21/0.45  thf('10', plain,
% 0.21/0.45      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k1_tarski @ sk_C)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('11', plain,
% 0.21/0.45      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.45         ((r2_hidden @ (k1_mcart_1 @ X10) @ X11)
% 0.21/0.45          | ~ (r2_hidden @ X10 @ (k2_zfmisc_1 @ X11 @ X12)))),
% 0.21/0.45      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.45  thf('12', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.21/0.45      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.45  thf('13', plain,
% 0.21/0.45      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))
% 0.21/0.45         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)))),
% 0.21/0.45      inference('split', [status(esa)], ['8'])).
% 0.21/0.45  thf('14', plain, (((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.21/0.45      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.45  thf('15', plain,
% 0.21/0.45      (~ (((k2_mcart_1 @ sk_A) = (sk_C))) | 
% 0.21/0.45       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.21/0.45      inference('split', [status(esa)], ['8'])).
% 0.21/0.45  thf('16', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.45      inference('sat_resolution*', [status(thm)], ['14', '15'])).
% 0.21/0.45  thf('17', plain, (((k2_mcart_1 @ sk_A) != (sk_C))),
% 0.21/0.45      inference('simpl_trail', [status(thm)], ['9', '16'])).
% 0.21/0.45  thf('18', plain, ($false),
% 0.21/0.45      inference('simplify_reflect-', [status(thm)], ['7', '17'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
